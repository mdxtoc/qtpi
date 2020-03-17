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
open Stringutils
open Listutils
open Functionutils
open Optionutils
open Sourcepos
open Instance
open Name
open Expr
open Braket
open Pattern
open Type
open Param
open Step
open Process
open Def
open Qsim
open Number
open Monenv
open Compile

open Value
open Prob
open Event

exception Error of sourcepos * string
exception MatchError of sourcepos * string
exception Disaster of sourcepos * string
exception LibraryError of string
exception BitOverflow of string
exception IntOverflow of string
exception FractionalInt of string
exception NegInt of string

let (<@>)  env n     = try Monenv.(<@>) env n 
                       with Not_found -> raise (Disaster (dummy_spos, 
                                                          Printf.sprintf "looking up %s in %s"
                                                                         (string_of_name n)
                                                                         (short_string_of_env env)
                                                         )
                                               )       

let miseval s v = raise (Error (dummy_spos, s ^ string_of_value v))

let unitv   = function VUnit           -> ()     | v -> miseval "unitv"    v
let bitv    = function VBit    b       -> b      | v -> miseval "bitv"     v
let numv    = function VNum    n       -> n      | v -> miseval "numv"     v
let boolv   = function VBool   b       -> b      | v -> miseval "boolv"    v
let charv   = function VChar   c       -> c      | v -> miseval "charv"    v
let stringv = function VString s       -> s      | v -> miseval "stringv"  v
let brav    = function VBra    b       -> b      | v -> miseval "brav"     v
let ketv    = function VKet    k       -> k      | v -> miseval "ketv"     v
let matrixv = function VMatrix m       -> m      | v -> miseval "matrixv"  v
let gatev   = function VGate   g       -> g      | v -> miseval "gatev"    v
let chanv   = function VChan   c       -> c      | v -> miseval "chanv"    v
let qbitv   = function VQbit   q       -> q      | v -> miseval "qbitv"    v
let qstatev = function VQstate s       -> s      | v -> miseval "qstatev"  v
let pairv   = function VTuple  [e1;e2] -> e1, e2 | v -> miseval "pairv"    v
let listv   = function VList   vs      -> vs     | v -> miseval "listv"    v
let funv    = function VFun    f       -> f      | v -> miseval "funv"     v

let vunit   ()      = VUnit
let vbit    b       = VBit    b
let vint    i       = VNum    (num_of_int i)              (* int -> value *)
let vnum    n       = VNum    n
let vbool   b       = VBool   b
let vchar   c       = VChar   c
let vstring s       = VString s
let vgate   g       = VGate   g
let vchan   c       = VChan   c
let vqbit   q       = VQbit   q
let vqstate s       = VQstate s
let vpair   (a,b)   = VTuple  [a;b]
let vtriple (a,b,c) = VTuple  [a;b;c]
let vlist   vs      = VList   vs
let vfun    f       = VFun    f

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

;; (* to give boyd a polytype *)

(* predefined channels *)
let dispose_c = -1
let out_c     = -2
let outq_c    = -3
let in_c      = -4

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
    let maybe b = if b then yes env else no () in
    match tinst pat, v with
    | PatAny            , _                 
    | PatUnit           , VUnit             
    | PatNil            , VList []          -> yes env
    | PatName   n       , _                 -> yes (env<@+>(n,v))
    | PatInt    i       , VNum    n         -> maybe (is_int n && num_of_int i =/ n)
    | PatBit    b       , VBit    b'        -> maybe (b=b')
    | PatBool   b       , VBool   b'        -> maybe (b=b')
    | PatChar   c       , VChar   c'        -> maybe (c=c')
    | PatString s       , VString s'        -> maybe (s=s')
    | PatBra    b       , VBra    b'        -> maybe (pv_of_braket b=b')
    | PatKet    k       , VKet    k'        -> maybe (pv_of_braket k=k')
    | PatCons   (ph,pt) , VList   (vh::vt)  -> succeed env (([ph;pt],[vh;VList vt])::work) rhs pairs
    | PatTuple  ps      , VTuple  vs        -> succeed env ((ps,vs)::work) rhs pairs
    | _                                     -> no () (* can happen: [] vs ::, :: vs [] *)
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
  
let rec evale env e =
  try
    match tinst e with
    | EUnit               -> VUnit
    | ENil                -> VList []
    | EVar n              -> (try env<@>n 
                              with Invalid_argument _ -> 
                                raise (Error (e.pos, "** Disaster: unbound " ^ string_of_name n))
                             )
    | ENum n              -> VNum n
    | EBool b             -> VBool b
    | EChar c             -> VChar c
    | EString s           -> VString s
    | EBit b              -> VBit b
    | EBra b              -> VBra (pv_of_braket b)
    | EKet k              -> VKet (pv_of_braket k)
    | EMinus e            -> VNum (~-/ (numev env e))
    | ENot   e            -> VBool (not (boolev env e))
    | ETuple es           -> VTuple (List.map (evale env) es)
    | ECons (hd,tl)       -> VList (evale env hd :: listev env tl)
    | ECond (c,e1,e2)     -> evale env (if boolev env c then e1 else e2)
    | EMatch (me,ems)     -> let v = evale env me in
                             (match matcher e.pos env ems v with
                              | Some (env, e) -> evale env e
                              | None          -> raise (MatchError (e.pos, Printf.sprintf "match failed against %s"
                                                                                          (string_of_value v)
                                                                   )
                                                            )
                             )  
    | EApp (f,a)          -> let fv = funev env f in
                             (try fv (evale env a) with LibraryError s -> raise (Error (e.pos, s)))

    | EArith (e1,op,e2)   -> (match op with
                              | Plus    -> VNum (numev env e1 +/ numev env e2)    
                              | Times   ->
                                  (let v1 = evale env e1 in
                                   let v2 = evale env e2 in
                                   match v1, v2 with
                                   | VNum    n1, VNum  n2   -> VNum (n1 */ n2)
                                   | VGate   g1, VGate g2   -> VGate (mult_gg g1 g2)
                                   | VKet     k, VBra  b    -> VMatrix (mult_kb k b)
                                   | VMatrix m1, VMatrix m2 -> VMatrix (mult_mm m1 m2)
                                   | _                      -> 
                                      raise (Disaster (e.pos, Printf.sprintf "multiply %s * %s" 
                                                                 (string_of_value v1) 
                                                                 (string_of_value v2)
                                                      )
                                            )
                                  )
                              | Minus   -> VNum (numev env e1 -/ numev env e2)
                              | Div     -> VNum (numev env e1 // numev env e2)
                              | Power   -> let v1 = numev env e1 in
                                           let v2 = numev env e2 in
                                           if is_int v2 then
                                             VNum (v1 **/ int_of_num v2)
                                           else raise (Error (e.pos, Printf.sprintf "fractional power: %s ** %s"
                                                                                    (string_of_num v1)
                                                                                    (string_of_num v2)
                                                             )
                                                      )
                              | Mod     -> let v1 = numev env e1 in
                                           let v2 = numev env e2 in
                                           if is_int v1 && is_int v2 then
                                             VNum (rem v1 v2)
                                           else raise (Error (e.pos, Printf.sprintf "fractional mod: %s %% %s"
                                                                                    (string_of_num v1)
                                                                                    (string_of_num v2)
                                                             )
                                                      )
                              | TensorProd -> 
                                  (let v1 = evale env e1 in
                                   let v2 = evale env e2 in
                                   match v1, v2 with
                                   | VGate   g1, VGate g2   -> VGate (tensor_gg g1 g2)
                                   | VBra    b1, VBra  b2   -> VBra (tensor_pv2 b1 b2)
                                   | VKet    k1, VKet  k2   -> VBra (tensor_pv2 k1 k2)
                                   | VMatrix m1, VMatrix m2 -> VMatrix (tensor_mm m1 m2)
                                   | _                      -> 
                                      raise (Disaster (e.pos, Printf.sprintf "tensor product %s >< %s" 
                                                                 (string_of_value v1) 
                                                                 (string_of_value v2)
                                                      )
                                            )
                                  )
                             )
    | ECompare (e1,op,e2) -> let v1 = evale env e1 in
                             let v2 = evale env e2 in
                             (try let c = deepcompare (v1,v2) in
                                  VBool (match op with
                                         | Eq  -> c=0
                                         | Neq -> c<>0
                                         | Lt  -> c<0
                                         | Leq -> c<=0
                                         | Geq -> c>=0
                                         | Gt  -> c>0
                                        )
                              with Disaster _ ->
                                   raise (Disaster (e.pos, Printf.sprintf "equality type failure; comparing %s:%s with %s:%s"
                                                                          (string_of_value v1)
                                                                          (string_of_type (type_of_expr e1))
                                                                          (string_of_value v2)
                                                                          (string_of_type (type_of_expr e2))
                                                   )
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
    | ELambda (pats, e)       -> fun_of e env pats
    | EWhere  (e, ed)         -> let env = match ed.inst with
                                           | EDPat (pat,_,we) ->
                                               let v = evale env we in
                                               bmatch env pat v
                                           | EDFun (fn,pats,_, we) ->
                                               let stored_env = ref env in
                                               let env = env <@+> bind_fun stored_env (tinst fn) pats we in
                                               stored_env := env;
                                               env
                                 in
                                 evale env e
  with 
  | MatchError (pos,s)  -> raise (MatchError (pos,s)) 
  | exn                 -> Printf.eprintf "\n** evale %s: %s %s sees exception %s\n" 
                                         (string_of_sourcepos e.pos)
                                         (short_string_of_env env)
                                         (string_of_expr e)
                                         (Printexc.to_string exn);
                           raise exn

(** Because we have nums in values we can't even use equality, I think.

    Comparison.  [compare x y] returns 0 if [x] equals [y],
    -1 if [x] is smaller than [y], and 1 if [x] is greater than [y].

    Note that Pervasive.compare can be used to compare reliably two integers
    only on OCaml 3.12.1 and later versions.
 *)

and deepcompare = function (* list everything to be sure I don't make a mistake *)
  | VNum     n1 , VNum     n2  -> Q.compare n1 n2
  | VTuple   v1s, VTuple   v2s  
  | VList    v1s, VList    v2s -> listcompare (v1s,v2s)
  | VFun     _  , VFun     _
  | VProcess _  , VProcess _
  | VChan    _  , VChan    _
  | VQstate  _  , VQstate  _
  | VQbit    _  , VQbit    _   -> raise (Can'tHappen "equality type failure")
  | VUnit       , VUnit        -> 0
  | VBit     v1 , VBit     v2  
  | VBool    v1 , VBool    v2  -> Stdlib.compare v1 v2 
  | VChar    v1 , VChar    v2  -> Stdlib.compare v1 v2 
  | VBra     v1 , VBra     v2  -> Stdlib.compare v1 v2
  | VKet     v1 , VKet     v2  -> Stdlib.compare v1 v2
  | VMatrix  v1 , VMatrix  v2  -> Stdlib.compare v1 v2
  | VGate    v1 , VGate    v2  -> Stdlib.compare v1 v2
  | VString  v1 , VString  v2  -> Stdlib.compare v1 v2    (* none of these hide values *)
  | _                          -> raise (Can'tHappen "deepcompare given different types")

and listcompare = function
| v1::v1s, v2::v2s -> (match deepcompare (v1,v2) with
                       | 0 -> listcompare (v1s,v2s)
                       | c -> c
                      )
| []     , []      -> 0
| []     , _       -> -1
| _      , []      -> 1

and fun_of expr env pats =
  match pats with
  | pat::pats -> VFun (fun v -> fun_of expr (bmatch env pat v) pats)
  | []        -> evale env expr

and bind_fun er n pats expr =
  let f v = 
     let env = !er in
     fun_of expr (bmatch env (List.hd pats) v) (List.tl pats)
   in
   (n, VFun f)
   
and unitev env e =
  match evale env e with
  | VUnit -> ()
  | v     -> mistyped e.pos (string_of_expr e) v (string_of_tnode Unit) 

and numev env e =
  match evale env e with
  | VNum i -> i
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

and qstateev env e = 
  match evale env e with
  | VQstate s -> s
  | v         -> mistyped e.pos (string_of_expr e) v "a qstate"

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

and gateev env e = 
  match evale env e with
  | VGate g -> g
  | v       -> mistyped e.pos (string_of_expr e) v "a gate"

let mkchan c traced = {cname=c; traced= traced;
                                stream=Queue.create (); 
                                rwaiters=PQueue.create 10; (* 10 is a guess *)
                                wwaiters=PQueue.create 10; (* 10 is a guess *)
                      }

module OrderedChan = struct type t = chan 
                            let compare c1 c2 = Stdlib.compare c1.cname c2.cname
                            let to_string = string_of_chan
                     end
module ChanSet = MySet.Make (OrderedChan)

type gsum = Grw of rwaiter | Gww of wwaiter

let stepcount = ref 0

let rec interp env proc =
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
  let newchan b = 
    let c = !chancount in 
    chancount := !chancount+1; 
    let chan = mkchan c b in
    VChan chan 
  in
  let (procnames: (name,unit) Hashtbl.t) = Hashtbl.create 100 in    
  let runners = PQueue.create (10) in (* 10 is a guess *)
  let addrunner runner = PQueue.push runners runner in
  let addnewproc name = 
    let rec adn i =
      let n = if i=0 then name else name ^ "(" ^ string_of_int i ^")" in
      try let _ = Hashtbl.find procnames n in adn (i+1)
      with Not_found -> Hashtbl.add procnames n (); n
    in 
    adn 0
  in
  let deleteproc n = Hashtbl.remove procnames n in
  let print_interp_state outstream =
    output_string outstream (Printf.sprintf "interpret\n runners=[\n  %s\n]\n channels=%s\n %s\n\n"
                                            (string_of_runnerqueue ";\n  " runners)
                                            (string_of_stuck_chans ())
                                            (String.concat "\n " (strings_of_qsystem ()))
                            )
  in
  let rec step () =
      if PQueue.is_empty runners then 
        (let string_of_stepcount () =
           if !Settings.showstepcount then
             Printf.sprintf "%d interpreter steps" !stepcount
           else ""
         in
         if !verbose || !verbose_interpret || !verbose_qsim || !show_final ||
            not (ChanSet.is_empty !stuck_chans)
         then
           Printf.printf "All %s! %s\n channels=%s\n %s\n\n"
                          (if ChanSet.is_empty !stuck_chans then "done" else "stuck")
                          (string_of_stepcount ())
                          (string_of_stuck_chans ())
                          (String.concat "\n " (strings_of_qsystem ()))
         else 
         if !pstep then
           Printf.printf "all done\n%s\n" (string_of_stepcount ())
         else 
           Printf.printf "\n%s\n" (string_of_stepcount ());
         if !traceevents then
           (Printf.printf "\nEvent Trace:\n\n";
            Event.show_trace ();
            Printf.printf "\n"
           )
        )
      else
        ((try 
            stepcount := !stepcount+1;
            if !verbose || !verbose_interpret then
              print_interp_state stdout;
            let runner = PQueue.pop runners in
            PQueue.excite runners;
            let pn, rproc, env = runner in
            let show_pstep s =
                 Printf.printf "%s: %s" pn s;
                 let _ = read_line () in
                 ()
            in
            let pstep_state env =
              let is_qbit = function (VQbit _) -> true
                            |        _         -> false
              in
              let env' = Monenv.filter (fun (_,v) -> is_qbit v) env in
              let env_string = if not (Monenv.null env') then 
                                 Printf.sprintf "  %s\n" (string_of_env env')
                               else ""
              in
              Printf.sprintf "%s  %s" env_string (string_of_qstate())
            in
            let pstep_env env' env =
              let assoc = assoc_of_monenv env in
              let assoc' = assoc_of_monenv env' in
              let assoc'' = take (List.length assoc' - List.length assoc)  assoc' in
              if assoc''<>[] then Printf.sprintf "\n  binds %s" (string_of_monassoc "=" string_of_value assoc'')
              else ""
            in
            (match rproc.inst with
             | Terminate           -> deleteproc pn; if !pstep then show_pstep "_0"
             | GoOnAs (gpn, es) -> 
                 (let vs = List.map (evale env) es in
                  try (match env<@>tinst gpn with
                       | VProcess (n, er, ns, proc) -> 
                           let locals = zip ns vs in
                           let env = monenv_of_lg locals !er in
                           deleteproc pn;
                           let gpn' = addnewproc n in
                           addrunner (gpn', proc, env);
                           if !traceId then trace (EVChangeId (pn, [gpn']));
                           if !pstep then
                             show_pstep (Printf.sprintf "%s(%s)" 
                                                        (tinst gpn) 
                                                        (string_of_list short_string_of_value "," vs)
                                        )
                       | v -> mistyped rproc.pos (string_of_name (tinst gpn)) v "a process"
                      )  
                  with Not_found -> raise (Error (dummy_spos, "** Disaster: no process called " ^ string_of_name (tinst gpn)))
                 )
             | WithNew ((traced, ps), proc) ->
                 let ps' = List.map (fun n -> (n, newchan traced)) (names_of_params ps) in
                 let env' = List.fold_left (<@+>) env ps' in
                 addrunner (pn, proc, env');
                 if !pstep then 
                   show_pstep (Printf.sprintf "(new %s)" (commasep (List.map string_of_param ps)))
             | WithQbit (qs, proc) ->
                 let ket_eval = function
                 | None      -> None
                 | Some kv   -> let k = ketv (evale env kv) in
                                (match pvsize k with
                                 | 2 -> Some k
                                 | _ -> raise (Error (rproc.pos, Printf.sprintf "qbit cannot be initialised to %s"
                                                                                  (string_of_ket k)
                                                         )
                                                  )
                                )
                 in
                 let qs' = List.map (fun (par,vopt) -> let n = name_of_param par in (n, newqbit pn n (ket_eval vopt))) qs in
                 let env' = List.fold_left (<@+>) env qs' in
                 addrunner (pn, proc, env');
                 if !pstep then 
                   show_pstep (Printf.sprintf "(newq %s)\n%s" (commasep (List.map string_of_qspec qs)) (pstep_state env'))
             | WithLet ((pat,e), proc) ->
                 let v = evale env e in
                 addrunner (pn, proc, bmatch env pat v);
                 if !pstep then 
                   show_pstep (Printf.sprintf "(let %s)" (string_of_letspec (pat,e)))
             | WithProc ((brec,pn',params,proc),p) ->
                 let er = ref env in
                 let procv = VProcess (tinst pn', er, names_of_params params, proc) in
                 let env = env<@+>(tinst pn', procv) in
                 if brec then er := env;
                 addrunner (pn, p, env)
             | WithQstep (qstep, proc) ->
                 (match qstep.inst with
                  | Measure (e, gopt, pat) -> let q = qbitev env e in
                                              (* measurement without detection is absurd, wrong. So disposed is always true *)
                                              let disposed = !measuredestroys in
                                              let qv, aqs = 
                                                if !traceevents then 
                                                  let qs = fst (qval q) in
                                                  List.hd (tev [q]), (if disposed then remove q qs else qs) 
                                                else 
                                                  "", [] 
                                              in
                                              let gv = (gateev env ||~~ g_I) gopt in
                                              let v = vbit (qmeasure disposed pn gv q = 1) in
                                              if !traceevents then trace (EVMeasure (pn, qv, gv, v, tev aqs));
                                              let env' = (match tinst pat with
                                                          | PatAny    -> env
                                                          | PatName n -> env <@+> (n,v)
                                                          | _         -> raise (Disaster (qstep.pos, string_of_qstep qstep))
                                                         )
                                              in
                                              addrunner (pn, proc, env');
                                              if !pstep then 
                                                show_pstep (Printf.sprintf "%s\n%s%s" (string_of_qstep qstep) 
                                                                                      (pstep_state env')
                                                                                      (pstep_env env' env)
                                                      )
                  | Ugatestep (es, g)      -> let qs = List.map (qbitev env) es in
                                              let g = gateev env g in
                                              let qvs = if !traceevents then tev qs else [] in
                                              ugstep pn qs g;
                                              addrunner (pn, proc, env);
                                              if !traceevents then trace (EVGate (pn, qvs, g, tev qs));
                                              if !pstep then 
                                                show_pstep (Printf.sprintf "%s\n%s" (string_of_qstep qstep) (pstep_state env))
                 )
             | GSum ioprocs      -> 
                 let withdraw chans = List.iter maybe_forget_chan chans in (* kill the space leak! *)
                 let canread pos c pat =
                   let can'tread s = raise (Error (pos, "cannot read from " ^ s ^ " channel (this should be a type error -- sorry)")) in
                   let do_match v' = Some (bmatch env pat v') in
                   try if c.cname = dispose_c then can'tread "dispose" 
                       else
                       if c.cname = out_c || c.cname = outq_c then can'tread "output"
                       else
                       if c.cname = in_c then 
                         (let v = vstring (read_line ()) in
                          if !traceIO then trace (EVInput (pn,v));
                          do_match v
                         )
                       else
                         let v' = Queue.pop c.stream in
                         (maybe_forget_chan c; do_match v')
                   with Queue.Empty ->
                   try boyd c.wwaiters; (* now the first must be alive *)
                       let (pn',v',proc',env'),gsir = PQueue.pop c.wwaiters in
                       let _, chans = !gsir in
                       gsir := false, [];
                       withdraw chans;
                       PQueue.excite c.wwaiters;
                       addrunner (pn', proc', env');
                       if !traceevents && c.traced then trace (EVMessage (c, pn', pn, v'));
                       do_match v'
                   with PQueue.Empty -> None
                 in
                 let canwrite pos c v =
                   let can'twrite s = raise (Error (pos, "cannot write to " ^ s ^ " channel (this should be a type error -- sorry)")) in
                   if c.cname = in_c then can'twrite "input"
                   else
                   if c.cname = dispose_c then 
                      (disposeqbit pn (qbitv v); 
                       if !traceevents then trace (EVDispose (pn,v));
                       true
                      )
                   else
                   if c.cname = out_c then
                     (let s = String.concat "" (List.map stringv (listv v)) in
                      print_string s; flush stdout; 
                      if !traceIO then trace (EVOutput (pn,vstring s));
                      true
                     )
                   else
                   if c.cname = outq_c then
                     (let s = qstatev v in
                      print_string s; flush stdout; 
                      if !traceIO then trace (EVOutput (pn,vstring s));
                      true
                     )
                   else
                   try boyd c.rwaiters;
                       let (pn',pat',proc',env'),gsir = PQueue.pop c.rwaiters in
                       let _, chans = !gsir in
                       gsir := false, [];
                       withdraw chans;
                       PQueue.excite c.rwaiters;
                       let v' = bmatch env' pat' v in
                       addrunner (pn', proc', v');
                       if !traceevents && c.traced then trace (EVMessage (c, pn, pn', v));
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
                                          (match canread iostep.pos c pat with
                                           | Some env' -> addrunner (pn, proc, env');
                                                          if !pstep then 
                                                            show_pstep (Printf.sprintf "%s%s\n" (string_of_iostep iostep) 
                                                                                                (pstep_env env env')
                                                                       )
                                           | None      -> try_iosteps ((c, Grw (pn, pat, proc, env))::gsum) pq
                                          )
                       | Write (ce,e)  -> let c = chanev env ce in
                                          let v = evale env e in
                                          if canwrite iostep.pos c v then 
                                            (addrunner (pn, proc, env);
                                             if !pstep then 
                                               show_pstep (Printf.sprintf "%s\n  sends %s" (string_of_iostep iostep) 
                                                                                           (string_of_value v)
                                                          )
                                            )
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
                   List.iter add_waiter gsum;
                   if !pstep then 
                     show_pstep (Printf.sprintf "%s\n  blocks" (short_string_of_process rproc))
                 in
                 let pq = PQueue.create (List.length ioprocs) in
                 List.iter (PQueue.push pq) ioprocs;
                 try_iosteps [] pq
             | TestPoint (n, p)  -> raise (Error (n.pos, "TestPoint not compiled"))
             | Iter _ -> raise (Error (proc.pos, "Iter not compiled"))
             | Cond (e, p1, p2)  ->
                 let bv = boolev env e in
                 addrunner (pn, (if bv then p1 else p2), env);
                 if !pstep then 
                   show_pstep (Printf.sprintf "%s (%B)" (short_string_of_process rproc) bv)
             | PMatch (e,pms)    -> 
                 let v = evale env e in
                 (match matcher rproc.pos env pms v with
                  | Some (env', proc) -> addrunner (pn, proc, env');
                                         if !pstep then 
                                           show_pstep (Printf.sprintf "%s\nchose %s%s" (short_string_of_process rproc)
                                                                                       (short_string_of_process proc)
                                                                                       (pstep_env env' env)
                                                      )
                  | None              -> raise (MatchError (rproc.pos, Printf.sprintf "match failed against %s"
                                                                                      (string_of_value v)
                                                           )
                                                )
                 )  
             | Par ps            ->
                 deleteproc pn;
                 let npns = 
                   List.fold_left  (fun ns (i,proc) -> let n = addnewproc (pn ^ "." ^ string_of_int i) in
                                                       addrunner (n, proc, env);
                                                       n::ns
                                   ) 
                                   []
                                   (numbered ps)
                 in
                 if !traceId then trace (EVChangeId (pn, List.rev npns));
                 if !pstep then 
                   show_pstep (short_string_of_process rproc)
            ) (* end of match *)
          with 
          | MatchError (pos,s)  -> raise (MatchError (pos,s)) 
          | exn                 ->
              Printf.eprintf "interpreter step () sees exception %s\n" (Printexc.to_string exn);
              print_interp_state stderr;
              raise exn
         ); (* end of try *)
         step()
       ) (* end of else *)
  in
  addrunner ("System", proc, env);
  step ()

(* Library 'declares' things by adding them to this list: name * type (as string) * value *)

let knowns = (ref [] : (name * string * value) list ref)

let know dec = knowns := dec :: !knowns

(* these are the built-in pdefs -- with newlines and spaces for offside parsing *)

let builtins = [
  "Iter (xs,P,iterc) =                          \n" ^
  "  match xs .                                 \n" ^
  "  + []    . iterc!() . _0                    \n" ^
  "  + x::xs . (new untraced callc)             \n" ^
  "            | P(x,callc)                     \n" ^
  "            | callc?(_) . Iter(xs,P,iterc)   \n"
  ;
  "Par (xs, P) =                                \n" ^
  "  match xs .                                 \n" ^
  "  + []     . _0                              \n" ^
  "  + x:: xs . | P(x)                          \n" ^
  "             | Par (xs, P)                   \n"
]

let bind_def env = function
  | Processdefs pdefs   -> let env = globalise env in
                           let er = ref env in
                           let env = globalise (List.fold_left (bind_pdef er) env pdefs) in
                           er := env;
                           env
  | Functiondefs fdefs  -> let env = globalise env in
                           let er = ref env in
                           let bind_fdef env (n, pats, _, expr) = env <@+> bind_fun er (tinst n) pats expr in
                           let env = globalise (List.fold_left bind_fdef env fdefs) in
                           er := env;
                           env
  | Letdef (pat, e)     -> (* not recursive, evaluate now *)
                           let v = evale env e in
                           globalise (bmatch env pat v)

let interpret defs =
  Random.self_init(); (* for all kinds of random things *)
  (* make an assoc list of library stuff *)
  let knownassoc = List.map (fun (n,_,v) -> n, v) !knowns in
  (* add standard channels *)
  let definitely_add env (name, c) =
    if env <@?> name then raise (LibraryError ("Whoops! Library has re-defined standard channel " ^ name))
    else env <@+> (name, VChan (mkchan c true))
  in
  let sysenv = globalise (List.fold_left definitely_add knownassoc 
                                            [("dispose", dispose_c); ("out", out_c); ("outq", outq_c); ("in", in_c)]) 
  in
  (* add built-ins *)
  let bipdefs = List.map compile_builtin (List.map Parseutils.parse_pdefstring builtins) in
  let er = ref sysenv in
  let sysenv = globalise (List.fold_left (bind_pdef er) sysenv bipdefs) in
  er := sysenv; 
  (* bind definitions in order *)
  let sysenv = globalise (List.fold_left bind_def sysenv defs) in
  if !verbose || !verbose_interpret then
    Printf.printf "sysenv = %s\n\n" (string_of_env sysenv);
  let sysv = try sysenv <@> "System"
             with Invalid_argument _ -> raise (Error (dummy_spos, "no System process"))
  in 
  match sysv with
  | VProcess (_, er, [], p) -> flush_all(); interp !er p
  | VProcess (_, _ , ps, _) -> raise (Error (dummy_spos, "can't interpret System with non-null parameter list"))
  | _                       -> raise (Error (dummy_spos, "no process named System"))
