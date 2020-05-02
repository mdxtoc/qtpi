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
open Functionutils
open Optionutils
open Listutils
open Sourcepos
open Instance
open Type
open Name
open Expr
open Pattern
open Process
open Param
open Step
open Def
open Monenv 
open Value

open Number
open Snum
open Vmg


exception CompileError of sourcepos * string
exception ExecutionError of sourcepos * string


(* ************************ 'compiling' sub-processes ************************ *)

let mon_name pn tpnum = "#mon#" ^ tinst pn ^ "#" ^ tpnum

let chan_name tpnum = "#chan#" ^ tpnum

let tadorn pos topt = adorn pos <.> twrap topt

let ut pos = Some (adorn pos Unit)
let cut pos = Some (adorn pos (Channel (adorn pos Unit)))

let insert_returns check rc proc =
  let bad pos s = raise (CompileError (pos, s ^ " not allowed in embedded process")) in
  let spos = steppos proc in
  let rec cmp proc =
    let ad = adorn spos in
    let adio = adorn spos in
    let ade = tadorn spos in
    match proc.inst with
    | Terminate     -> Some (ad (GSum [adio (Write (ade (cut spos) (EVar rc), ade (ut spos) EUnit)), proc]))
    | GoOnAs _      -> if check then bad spos "process invocation" else None
    | Par _         -> if check then bad spos "parallel sum" else None
    | WithNew _     
    | WithQbit _    
    | WithLet _
    | WithProc _    
    | WithQstep _ 
    | JoinQs _
    | SplitQs _
    | GSum _
    | Cond    _
    | PMatch  _     
    | TestPoint _   
    | Iter _        -> None
  in
  Process.map cmp proc

(* Here is where we apply restrictions on monitor processes:
    no Reading   (it's outside the protocol, so no input)
    no Calling
    no new qbits (it's outside the protocol, so no quantum stuff)
    no gating    (ditto)
    no measuring (ditto)
    no Testpoint (come along now)
    no Par
 *)
 
let precompile_monbody tpnum proc =
  let bad pos s = raise (CompileError (pos, s ^ " not allowed in monitor process")) in
  let rec check proc =
    match proc.inst with
    | Terminate     -> None (* will be done in insert_returns *)
    | GSum iops     -> let ciop (iostep, _) = 
                         match iostep.inst with
                         | Write (ce,_) -> if not (Type.is_classical (type_of_expr ce)) then
                                             bad iostep.pos "non-classical channel"
                         | _            -> bad iostep.pos "message receive"
                       in
                       List.iter ciop iops; None
    | GoOnAs _      -> bad proc.pos "process invocation"
    | WithQbit _    -> bad proc.pos "qbit creation"
    | WithQstep _   -> bad proc.pos "qbit gating/measuring"
    | WithProc _    -> bad proc.pos "process definition"
    | JoinQs _      -> bad proc.pos "joining qbit collections"
    | SplitQs _     -> bad proc.pos "splitting qbit collection"
    | TestPoint _   -> bad proc.pos "test point"
    | Iter _        -> raise (CompileError (proc.pos, "Can't compile Iter in precompile_monbody yet"))
    | Par _         -> bad proc.pos "parallel sum"
    | WithNew _     
    | WithLet _
    | Cond    _
    | PMatch  _     -> None
  in
  let _ = Process.map check proc in
  let rc = chan_name tpnum in
  insert_returns true rc proc

let precompile_proc env pn mon proc =
  (* if !verbose || !verbose_compile then
       Printf.printf "precompile_proc env=%s\n  pn=%s\n  mon=(%s)\n proc=(%s)\n"
                       (string_of_env env)
                       (tinst pn)
                       (string_of_monitor mon)
                       (string_of_process proc); *)
  let construct_callpar pos rc call p =
    let read = adorn pos (Read (tadorn pos (cut pos) (EVar rc), tadorn pos (ut pos) PatAny)) in
    let gsum = adorn pos (GSum [(read, p)]) in
    adorn pos (Par [call; gsum])
  in
  let rec cmp spos proc =
    let ad = adorn spos in
    let ade = tadorn spos in
    let adpar = tadorn spos in
    let adn = tadorn spos in
    match proc.inst with
    | TestPoint (tpn, p) -> let p = Process.map (cmp spos) p in
                            let rc = chan_name tpn.inst in
                            let mn = mon_name pn tpn.inst in
                            let tp = Some (adorn spos (Process [])) in
                            let call = ad (GoOnAs (adn tp mn, [])) in
                            let par = construct_callpar tpn.pos rc call p in
                            let (_, monproc) = _The (find_monel tpn.inst mon) in
                            let def = ad (WithProc ((false, adn tp mn, [], precompile_monbody tpn.inst monproc), par)) in
                            let mkchan = ad (WithNew ((false,[adpar (cut spos) rc]), def)) in
                            Some mkchan
    | WithProc  ((brec,pn,params,proc),p) 
                         -> let p = Process.map (cmp spos) p in
                            let proc = Process.map (cmp spos) proc in
                            Some (ad (WithProc ((brec,pn,params,proc),p)))
    | Iter (pat, e, ip, p)
                         -> let p = Process.map (cmp spos) p in
                            let rc = chan_name (short_string_of_sourcepos ip.pos) in
                            let ipname = "#proc#" ^ (short_string_of_sourcepos ip.pos) in
                            let xname = "x#" in
                            let cname = "c#" in
                            let callIter = ad (GoOnAs (adn None "Iter#", [e; ade None (EVar ipname); ade None (EVar rc)])) in
                            let par = construct_callpar ip.pos rc callIter p in
                            let ip = insert_returns true cname ip in
                            let ip = Process.map (cmp spos) ip in
                            let ip = ad (WithLet ((pat, ade None (EVar xname)),ip)) in
                            let def = ad (WithProc ((false, adn None ipname, [adpar None xname; adpar None cname], ip), par)) in
                            let mkchan = ad (WithNew ((false, [adpar None rc]), def)) in
                            Some mkchan
    | Terminate 
    | GoOnAs    _      
    | WithNew   _
    | WithQbit  _
    | WithLet   _
    | WithQstep _
    | JoinQs    _
    | SplitQs   _
    | Cond      _
    | PMatch    _
    | GSum      _
    | Par       _        -> None
  in
  env, Process.map (cmp (steppos proc)) proc

(* I think this should be in Interpret, but then I think it should be here, but then ... *)
let bind_pdef er env (pn,params,p,mon as pdef) =
  let env, proc = precompile_proc env pn mon p in
  if (!verbose || !verbose_compile) && p<>proc then
    Printf.printf "Expanding .....\n%s....... =>\n%s\n.........\n\n"
                    (string_of_pdef pdef)
                    (string_of_process proc);
  env <@+> (tinst pn, of_procv (tinst pn, er, names_of_params params, proc))

let precompile_builtin (pn,params,p,mon as pdef) =
  if !verbose || !verbose_compile then
    Printf.printf "precompiling built-in %s\n" (string_of_pdef pdef);
  if not (null mon) then
    raise (Settings.Error (Printf.sprintf "built_in %s has logging sub-processes" (string_of_typedname pn)));
  (* all we do is append a # to the name in recursive calls ... *)
  let pname = tinst pn in
  let pname' = pname ^ "#" in
  let hash pn = {pn with inst = {pn.inst with tinst = pname'}} in
  let cmp proc =
    match proc.inst with
    | GoOnAs (pn',args) 
      when tinst pn' = pname -> Some (adorn proc.pos (GoOnAs (hash pn', args)))
    | _                      -> None
  in
  let pdef' = (hash pn, params, Process.map cmp p, mon) in
  if !verbose || !verbose_compile then
    Printf.printf "precompiled to %s\n\n" (string_of_pdef pdef');
  pdef'

(* ************************ compiling typed expressions into functions ************************ *)

(** Because we have nums in values we can't even use equality, I think.

    Comparison.  [compare x y] returns 0 if [x] equals [y],
    -1 if [x] is smaller than [y], and 1 if [x] is greater than [y].

    Note that Pervasive.compare can be used to compare reliably two integers
    only on OCaml 3.12.1 and later versions.
 *)

let rec deepcompare t v1 v2 = (* list everything to be sure I don't make a mistake *)
  match t.inst with
  | Unit      -> 0
  | Num       -> Q.compare (to_num v1) (to_num v2)
  | Tuple ts  -> tupcompare ts (to_list v1) (to_list v2)
  | List  t   -> listcompare t (to_list v1) (to_list v2)
  | Bit       
  | Bool       
  | Char
  | Sxnum
  | Bra     
  | Ket       
  | Matrix    
  | Gate      -> Stdlib.compare v1 v2
  | Fun     _ 
  | Process _  
  | Channel _  
  | Qstate   
  | Qbit
  | Qbits     
  | Unknown _
  | Known   _
  | Poly    _ -> raise (Can'tHappen (Printf.sprintf "deepcompare type %s" (string_of_type t)))

and listcompare t v1s v2s =
  match v1s, v2s with
  | v1::v1s, v2::v2s ->  (match deepcompare t v1 v2 with
                          | 0 -> listcompare t v1s v2s
                          | c -> c
                         )
  | []     , []      ->  0
  | []     , _       -> -1
  | _      , []      ->  1

and tupcompare ts v1s v2s =
  match ts, v1s, v2s with
  | t::ts, v1::v1s, v2::v2s -> (match deepcompare t v1 v2 with
                                | 0 -> tupcompare ts v1s v2s
                                | c -> c
                               )
  | []   , []     , []      -> 0
  | _                       -> raise (Can'tHappen (Printf.sprintf "tupcompare %s %s %s" 
                                                                      (bracketed_string_of_list string_of_type ts)
                                                                      (bracketed_string_of_list (fun _ -> "?") v1s)
                                                                      (bracketed_string_of_list (fun _ -> "?") v2s)
                                                  )
                                     )

let cconst : vt -> env -> vt = fun v env -> v
;;

let rec compile_expr : expr -> (env -> vt) = fun e ->
  if !verbose || !verbose_compile then
    (Printf.printf "compile_expr %s\n" (string_of_expr e); flush_all());
  let et = type_of_expr e in
  let can'thappen () = raise (Can'tHappen (Printf.sprintf "compile_expr %s type %s" (string_of_expr e) (string_of_type et))) in

  let intc : sourcepos -> string -> vt -> int = fun pos str v -> 
    let n = to_num v in
    if is_int n then int_of_num n
    else raise (ExecutionError (e.pos, Printf.sprintf "%s: %s" str (string_of_num n)))
  in
  let nonnegintc : sourcepos -> string -> vt -> int = fun pos str v -> 
    let i = intc pos ("fractional " ^ str) v in
    if i>=0 then i
    else raise (ExecutionError (e.pos, Printf.sprintf "negative %s: %s" str (string_of_int i)))
  in
  
  match tinst e with
  | EUnit           -> cconst (of_unit ())
  | EVar n          -> fun env -> env <@> n 
  | ENum num        -> cconst (of_num num)
  | EBool b         -> cconst (of_bool b)
  | EChar uc        -> cconst (of_uchar uc)
  | EString ucs     -> cconst (of_uchars ucs)
  | EBit b          -> cconst (of_bit b)
  | EBra b          -> cconst (of_nv (nv_of_braket b))
  | EKet k          -> cconst (of_nv (nv_of_braket k))
  | EMinus e        -> (* overloaded *)
      (let f = compile_expr e in
       match et.inst with
       | Num   -> fun env -> of_num (~-/(to_num (f env)))
       | Sxnum -> fun env -> of_csnum (Snum.cneg (to_csnum (f env)))
       | _     -> can'thappen ()
      )
  | ENot e          ->
      (let f = compile_expr e in
       fun env -> of_bool (not (to_bool (f env)))
      )
  | EDagger e       -> (* overloaded *)
      (let f = compile_expr e in
       match et.inst with
       | Gate   -> fun env -> of_gate (dagger_g (to_gate (f env)))
       | Matrix -> fun env -> of_matrix (dagger_m (to_matrix (f env)))
       | _      -> can'thappen ()
      )
  | ETuple es       ->
      (let apply env f = f env in
       let fs = List.map compile_expr es in
       fun env -> of_tuple (List.map (apply env) fs)
      )
  | ENil        -> cconst (of_list [])
  | ERes w      -> 
      (match et.inst with
       | Fun (t,_) ->
           (match w with
            | ResShow -> 
                let f = let optf t = match t.inst with
                                     | Qbits     -> Some "<qbit>"
                                     | Qstate    -> Some "<qstate>"
                                     | Fun     _ -> Some "<function>"
                                     | Channel _ -> Some "<channel>"
                                     | Process _ -> Some "<process>"
                                     | _         -> None
                        in
                        so_value optf t
                in
                fun env -> of_fun (hide_string <.> f)
            | ResCompare ->
                ((match t.inst with
                  | Unknown _
                  | Known _
                  | Poly _       -> raise (CompileError (e.pos, (Printf.sprintf "'compare' used with poly-type %s" 
                                                                                    (string_of_type t)
                                                                )
                                                        )
                                         )
                  | _            -> ()
                 );
                 let f = deepcompare t in
                 fun env -> of_fun (fun v -> of_fun (fun v' -> hide_int (f v v')))
                )
           )
       | _         -> raise (Can'tHappen (Printf.sprintf "%s %s" (string_of_expr e) (string_of_type et)))
      )
  | ECons (e1,e2)   ->
      (let f1 = compile_expr e1 in
       let f2 = compile_expr e2 in
       fun env -> of_list (f1 env :: (to_list (f2 env)))
      )
  | EAppend (e1,e2)     ->
      (let f1 = compile_expr e1 in
       let f2 = compile_expr e2 in
       fun env -> of_list (List.append (to_list (f1 env)) (to_list (f2 env)))
      )
  | ECond (ce,te,ee)    ->
      (let cf = compile_expr ce in
       let tf = compile_expr te in
       let ef = compile_expr ee in
       (fun env -> (if (to_bool (cf env)) then tf else ef) env)
      )
  | EJux (fe,ae)        ->
      (let ff = compile_expr fe in
       let af = compile_expr ae in
       (fun env -> try (to_fun (ff env)) (af env)
                   with LibraryError s -> raise (ExecutionError (e.pos, s))
       )
      )
    
  | EArith (e1,op,e2)  ->
      (let f1 = compile_expr e1 in
       let f2 = compile_expr e2 in
       match op with
       | Plus            
       | Minus      ->
           (match (type_of_expr e1).inst with
            | Num    -> let f = if op=Plus then (+/) else (-/) in
                        fun env -> of_num (f (to_num (f1 env)) (to_num (f2 env)))
            | Matrix -> let f = if op=Plus then add_mm else sub_mm in
                        fun env -> of_matrix (f (to_matrix (f1 env)) (to_matrix (f2 env)))
            | Sxnum  -> let f = if op=Plus then Snum.csum else Snum.cdiff in
                        fun env -> of_csnum (f (to_csnum (f1 env)) (to_csnum (f2 env)))
            | _      -> can'thappen ()
           )
       | Times      ->
           (match (type_of_expr e1).inst, (type_of_expr e2).inst with
            | Num   , Num    -> fun env -> of_num ((to_num (f1 env)) */ (to_num (f2 env)))
            | Sxnum , Sxnum  -> fun env -> of_csnum (cprod (to_csnum (f1 env)) (to_csnum (f2 env)))
            | Gate  , Gate   -> fun env -> of_gate (mult_gg (to_gate (f1 env)) (to_gate (f2 env)))
            | Ket   , Bra    -> fun env -> of_matrix (mult_kb (to_ket (f1 env)) (to_bra (f2 env)))
            | Matrix, Matrix -> fun env -> of_matrix (mult_mm (to_matrix (f1 env)) (to_matrix (f2 env)))
            | Sxnum , Matrix -> fun env -> of_matrix (mult_nm (to_csnum (f1 env)) (to_matrix (f2 env)))
            | Matrix, Sxnum  -> fun env -> of_matrix (mult_nm (to_csnum (f2 env)) (to_matrix (f1 env)))
            | _                         -> can'thappen()
           )
       | Div        -> fun env -> of_num (to_num (f1 env) // to_num (f2 env))
       | Power      -> fun env -> of_num (to_num (f1 env) **/ intc e2.pos "fractional power" (f2 env))
       | Mod        -> fun env -> of_num (to_num (f1 env) **/ intc e2.pos "fractional mod" (f2 env))
       | TensorProd -> (* overloaded *)
           (match (type_of_expr e1).inst with
            | Gate   -> fun env -> of_gate (tensor_gg (to_gate (f1 env)) (to_gate (f2 env)))
            | Bra  
            | Ket    -> fun env -> of_nv (tensor_nvnv (to_nv (f1 env)) (to_nv (f2 env)))
            | Matrix -> fun env -> of_matrix (tensor_mm (to_matrix (f1 env)) (to_matrix (f2 env)))
            | _      -> can'thappen()
           )
       | TensorPower ->
           (let powc = nonnegintc e2.pos "tensor-power exponent" in
            match (type_of_expr e1).inst with
            | Gate   -> fun env -> of_gate (tensorpow_g (to_gate (f1 env)) (powc (f2 env)))
            | Bra    
            | Ket    -> fun env -> of_nv (tensorpow_nv (to_nv (f1 env)) (powc (f2 env)))
            | Matrix -> fun env -> of_matrix (tensorpow_m (to_matrix (f1 env)) (powc (f2 env)))
            | _      -> can'thappen()
           )
      )
  | ECompare (e1,op,e2) ->
      (let f1 = compile_expr e1 in
       let f2 = compile_expr e2 in
       let t = type_of_expr e1 in
       let cf = match op with
                | Eq  -> ((=)0)  <..> Stdlib.compare
                | Neq -> ((<>)0) <..> Stdlib.compare
                | Lt  -> ((<)0)  <..> deepcompare t
                | Leq -> ((<=)0) <..> deepcompare t
                | Geq -> ((>=)0) <..> deepcompare t
                | Gt  -> ((>)0)  <..> deepcompare t
       in
       fun env -> of_bool (cf (f1 env) (f2 env))
      )
  | EBoolArith (e1,op,e2)   ->
      (let f1 = compile_expr e1 in
       let f2 = compile_expr e2 in
       let f = match op with
               | And       -> (&&)
               | Or        -> (||)
               | Implies   -> (fun b1 b2 -> (not b1) || b2)
               | Iff       -> (=)
       in
       fun env -> of_bool (f (to_bool (f1 env)) (to_bool (f2 env)))
      )
  | ESub (e1,e2)            ->
      (let f1 = to_list <.> compile_expr e1 in
       let f2 = nonnegintc e2.pos "subscript" <.> compile_expr e2 in
       fun env -> (try List.nth (f1 env) (f2 env)
                   with _ -> raise (ExecutionError (e.pos, Printf.sprintf "subscript %d not in range of qbits collection length %d"
                                                             (f2 env)
                                                             (List.length (f1 env))
                                          )
                                   )
                  )
      )
  | EMatch  (me,ems)     -> let fe = compile_expr me in
                            let fm = compile_match e.pos string_of_expr compile_expr ems in
                            fun env -> fm (fe env) env
  | ELambda _ (*of pattern list * expr*)
  | EWhere  _ (*of expr * edecl*)
                            -> raise (CompileError(e.pos, Printf.sprintf "can't (yet) compile %s" (string_of_expr e)))

(* Sestoft's naive pattern matcher, from "ML pattern match and partial evaluation".
   Modified a bit, obvs, but really the thing.
   Modified again to be a compiler
 *)

and compile_match : sourcepos -> ('a -> string) -> ('a -> 'b) -> (pattern * 'a) list -> (vt -> 'b) = 
                    fun pos string_of_a compile_a pairs ->
  let dtree = Matchcheck.match_dtree false string_of_expr pairs in
  if !verbose || !verbose_compile then
    Printf.printf "matcher %s %s\ndtree = %s\n\n -- that's all\n" 
                    (string_of_sourcepos pos)
                    (Matchcheck.string_of_rules string_of_a pairs)
                    (Matchcheck.string_of_dtree string_of_expr dtree);
  raise (CompileError (pos, "no compile_match yet"))
   
(* let bmatch env pat t v =
  match matcher pat.pos env [pat,()] t v with
  | Some (env,()) -> env
  | None          -> raise (Disaster (pat.pos,
                                      Printf.sprintf "bmatch %s %s"
                                                     (string_of_pattern pat)
                                                     (string_of_value t v)
                                     )
                           ) *)
  

module CExprH = struct type t = expr 
                       let equal = (==) (* yes, identity, not equality *)
                       let hash = Hashtbl.hash
                       let to_string = string_of_expr
                end
module CExprHash = MyHash.Make (CExprH)

let compiletab = CExprHash.create 1000

let compile_expr = CExprHash.memofun compiletab compile_expr
