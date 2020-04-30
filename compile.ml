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
open Value

open Number
open Snum
open Vmg

open Monenv (* do this last so we get the weird execution environment mechanism *)

exception Error of sourcepos * string

(* ************************ 'compiling' sub-processes ************************ *)

let mon_name pn tpnum = "#mon#" ^ tinst pn ^ "#" ^ tpnum

let chan_name tpnum = "#chan#" ^ tpnum

let insert_returns check rc proc =
  let bad pos s = raise (Error (pos, s ^ " not allowed in embedded process")) in
  let rec cmp proc =
    let ad = adorn proc.pos in
    let adio = adorn proc.pos in
    let ade = tadorn proc.pos in
    match proc.inst with
    | Terminate     -> Some (ad (GSum [adio (Write (ade (EVar rc), ade EUnit)), proc]))
    | GoOnAs _      -> if check then bad proc.pos "process invocation" else None
    | Par _         -> if check then bad proc.pos "parallel sum" else None
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
 
let compile_monbody tpnum proc =
  let bad pos s = raise (Error (pos, s ^ " not allowed in monitor process")) in
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
    | Iter _        -> raise (Error (proc.pos, "Can't compile Iter in compile_monbody yet"))
    | Par _         -> bad proc.pos "parallel sum"
    | WithNew _     
    | WithLet _
    | Cond    _
    | PMatch  _     -> None
  in
  let _ = Process.map check proc in
  let rc = chan_name tpnum in
  insert_returns true rc proc

let compile_proc env pn mon proc =
  (* if !verbose || !verbose_compile then
       Printf.printf "compile_proc env=%s\n  pn=%s\n  mon=(%s)\n proc=(%s)\n"
                       (string_of_env env)
                       (tinst pn)
                       (string_of_monitor mon)
                       (string_of_process proc); *)
  let construct_callpar pos rc call p =
    let read = adorn pos (Read (tadorn pos (EVar rc), tadorn pos PatAny)) in
    let gsum = adorn pos (GSum [(read, p)]) in
    adorn pos (Par [call; gsum])
  in
  let rec cmp proc =
    let ad = adorn proc.pos in
    let ade = tadorn proc.pos in
    let adpar = tadorn proc.pos in
    let adn = tadorn proc.pos in
    match proc.inst with
    | TestPoint (tpn, p) -> let p = Process.map cmp p in
                            let rc = chan_name tpn.inst in
                            let mn = mon_name pn tpn.inst in
                            let call = ad (GoOnAs (adn mn, [])) in
                            let par = construct_callpar tpn.pos rc call p in
                            let (_, monproc) = _The (find_monel tpn.inst mon) in
                            let def = ad (WithProc ((false, adn mn, [], compile_monbody tpn.inst monproc), par)) in
                            let mkchan = ad (WithNew ((false,[adpar rc]), def)) in
                            Some mkchan
    | WithProc  ((brec,pn,params,proc),p) 
                         -> let p = Process.map cmp p in
                            let proc = Process.map cmp proc in
                            Some (ad (WithProc ((brec,pn,params,proc),p)))
    | Iter (pat, e, ip, p)
                         -> let p = Process.map cmp p in
                            let rc = chan_name (short_string_of_sourcepos ip.pos) in
                            let ipname = "#proc#" ^ (short_string_of_sourcepos ip.pos) in
                            let xname = "x#" in
                            let cname = "c#" in
                            let callIter = ad (GoOnAs (adn "Iter#", [e; ade (EVar ipname); ade (EVar rc)])) in
                            let par = construct_callpar ip.pos rc callIter p in
                            let ip = insert_returns true cname ip in
                            let ip = Process.map cmp ip in
                            let ip = ad (WithLet ((pat, ade (EVar xname)),ip)) in
                            let def = ad (WithProc ((false, adn ipname, [adpar xname; adpar cname], ip), par)) in
                            let mkchan = ad (WithNew ((false, [adpar rc]), def)) in
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
  env, Process.map cmp proc

(* I think this should be in Interpret, but then I think it should be here, but then ... *)
let bind_pdef er env (pn,params,p,mon as pdef) =
  let env, proc = compile_proc env pn mon p in
  if (!verbose || !verbose_compile) && p<>proc then
    Printf.printf "Compiling .....\n%s....... =>\n%s\n.........\n\n"
                    (string_of_pdef pdef)
                    (string_of_process proc);
  env <@+> (tinst pn, VProcess (tinst pn,er, names_of_params params, proc))

let compile_builtin (pn,params,p,mon as pdef) =
  if !verbose || !verbose_compile then
    Printf.printf "compiling built-in %s\n" (string_of_pdef pdef);
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
    Printf.printf "compiled to %s\n\n" (string_of_pdef pdef');
  pdef'

(* ************************ compiling typed expressions into functions ************************ *)

exception CompileError of sourcepos * string

(* I make heavy use of Obj.magic here. Type value is a place holder *)

(* for the moment I'm still using an assoc list as environment *)

let boolc   : value -> bool       = Obj.magic
let csnumc  : value -> csnum      = Obj.magic
let gatec   : value -> gate       = Obj.magic
let listc   : value -> value list = Obj.magic
let matrixc : value -> matrix     = Obj.magic
let numc    : value -> num        = Obj.magic
let nvc     : value -> nv         = Obj.magic
let ucharc  : value -> Uchar.t    = Obj.magic
let valuec  : 'a    -> value      = Obj.magic

(** Because we have nums in values we can't even use equality, I think.

    Comparison.  [compare x y] returns 0 if [x] equals [y],
    -1 if [x] is smaller than [y], and 1 if [x] is greater than [y].

    Note that Pervasive.compare can be used to compare reliably two integers
    only on OCaml 3.12.1 and later versions.
 *)

let rec deepcompare t v1 v2 = (* list everything to be sure I don't make a mistake *)
  match t.inst with
  | Unit      -> 0
  | Num       -> Q.compare (numc v1) (numc v2)
  | Tuple ts  -> tupcompare ts (listc v1) (listc v2)
  | List  t   -> listcompare t (listc v1) (listc v2)
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
  | v1::v1s, v2::v2s -> (match deepcompare t v1 v2 with
                         | 0 -> listcompare t v1s v2s
                         | c -> c
                        )
  | []     , []      -> 0
  | []     , _       -> -1
  | _      , []      -> 1

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

let rec compile_expr : expr -> (value monenv -> value) = fun e ->
  let t = type_of_expr e in
  let simple e env = (Obj.magic e : value) in
  let canthappen () = raise (Can'tHappen (Printf.sprintf "compile_expr %s type %s" (string_of_expr e) (string_of_type t))) in

  let intc : sourcepos -> string -> value -> int = fun pos str v -> 
    let n = numc v in
    if is_int n then int_of_num n
    else raise (Error (e.pos, Printf.sprintf "%s: %s" str (string_of_num n)))
  in
  let nonnegintc : sourcepos -> string -> value -> int = fun pos str v -> 
    let i = intc pos ("fractional " ^ str) v in
    if i>=0 then i
    else raise (Error (e.pos, Printf.sprintf "negative %s: %s" str (string_of_int i)))
  in
  
  match tinst e with
  | EUnit           -> simple ()
  | EVar n          -> (fun env -> env <@> n)
  | ENum num        -> simple num
  | EBool b         -> simple b
  | EChar uc        -> simple uc
  | EString ucs     -> simple ucs
  | EBit b          -> simple b
  | EBra b          -> simple b
  | EKet k          -> simple k
  | EMinus e        -> (* overloaded *)
      (let f = compile_expr e in
       match t.inst with
       | Num   -> (fun env -> valuec (~-/(numc (f env))))
       | Sxnum -> (fun env -> (Obj.magic (Snum.cneg (Obj.magic (f env):csnum)):value))
       | _     -> canthappen ()
      )
  | ENot e          ->
      (let f = compile_expr e in
       (fun env -> (Obj.magic (not (Obj.magic (f env):bool)):value))
      )
  | EDagger e       -> (* overloaded *)
      (let f = compile_expr e in
       match t.inst with
       | Gate   -> (fun env -> (Obj.magic (dagger_g (Obj.magic (f env):gate)):value))
       | Matrix -> (fun env -> (Obj.magic (dagger_m (Obj.magic (f env):matrix)):value))
       | _      -> canthappen ()
      )
  | ETuple es       ->
      (let apply env f = f env in
       let fs = List.map compile_expr es in
       (fun env -> (Obj.magic (List.map (apply env) fs) :value))
      )
  | ENil        -> simple []
  | ECons (e1,e2)   ->
      (let f1 = compile_expr e1 in
       let f2 = compile_expr e2 in
       (fun env -> (Obj.magic (f1 env :: (Obj.magic (f2 env) :value list)) :value))
      )
  | EAppend (e1,e2)     ->
      (let f1 = compile_expr e1 in
       let f2 = compile_expr e2 in
       (fun env -> (Obj.magic (List.append (Obj.magic (f1 env) :value list) (Obj.magic (f2 env) :value list)) :value))
      )
  | ECond (ce,te,ee)    ->
      (let cf = compile_expr ce in
       let tf = compile_expr te in
       let ef = compile_expr ee in
       (fun env -> if (Obj.magic (cf env) :bool) then tf env else ef env)
      )
  | EJux (fe,ae)        ->
      (let ff = compile_expr fe in
       let af = compile_expr ae in
       (fun env -> try (Obj.magic (ff env) :value->value) (af env)
                   with LibraryError s -> raise (Error (e.pos, s))
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
                        (fun env -> valuec (f (numc (f1 env)) (numc (f2 env))))
            | Matrix -> let f = if op=Plus then add_mm else sub_mm in
                        (fun env -> valuec (f (matrixc (f1 env)) (matrixc (f2 env))))
            | Sxnum  -> let f = if op=Plus then Snum.csum else Snum.cdiff in
                        (fun env -> valuec (f (csnumc (f1 env)) (csnumc (f2 env))))
            | _      -> canthappen ()
           )
       | Times      ->
           (match (type_of_expr e1).inst, (type_of_expr e2).inst with
            | Num   , Num    -> (fun env -> (Obj.magic ((Obj.magic (f1 env):num) */ (Obj.magic (f2 env):num)) :value))
            | Sxnum , Sxnum  -> (fun env -> (Obj.magic (cprod (Obj.magic (f1 env):csnum) (Obj.magic (f2 env):csnum)) :value))
            | Gate  , Gate   -> (fun env -> (Obj.magic (mult_gg (Obj.magic (f1 env):gate) (Obj.magic (f2 env):gate)) :value))
            | Ket   , Bra    -> (fun env -> valuec (mult_kb (nvc (f1 env)) (nvc (f2 env))))
            | Matrix, Matrix -> (fun env -> (Obj.magic (mult_mm (Obj.magic (f1 env):matrix) (Obj.magic (f2 env):matrix)) :value))
            | Sxnum , Matrix -> (fun env -> valuec (mult_nm (csnumc (f1 env)) (matrixc (f2 env))))
            | Matrix, Sxnum  -> (fun env -> valuec (mult_nm (csnumc (f2 env)) (matrixc (f1 env))))
            | _                          -> canthappen()
           )
       | Div        -> (fun env -> valuec (numc (f1 env) // numc (f2 env)))
       | Power      -> (fun env -> valuec (numc (f1 env) **/ intc e2.pos "fractional power" (f2 env)))
       | Mod        -> (fun env -> valuec (numc (f1 env) **/ intc e2.pos "fractional mod" (f2 env)))
       | TensorProd -> (* overloaded *)
           (match (type_of_expr e1).inst with
            | Gate   -> (fun env -> valuec (tensor_gg (gatec (f1 env)) (gatec (f2 env))))
            | Bra  
            | Ket    -> (fun env -> valuec (tensor_nvnv (nvc (f1 env)) (nvc (f2 env))))
            | Matrix -> (fun env -> valuec (tensor_mm (matrixc (f1 env)) (matrixc (f2 env))))
            | _      -> canthappen()
           )
       | TensorPower ->
           (let powc = nonnegintc e2.pos "tensor-power exponent" in
            match (type_of_expr e1).inst with
            | Gate   -> (fun env -> valuec (tensorpow_g (gatec (f1 env)) (powc (f2 env))))
            | Bra    
            | Ket    -> (fun env ->  valuec (tensorpow_nv (nvc (f1 env)) (powc (f2 env))))
            | Matrix -> fun env -> valuec (tensorpow_m (matrixc (f1 env)) (powc (f2 env)))
            | _      -> canthappen()
           )
      )
  | ECompare (e1,op,e2) ->
      (let f1 = compile_expr e1 in
       let f2 = compile_expr e2 in
       let t = type_of_expr e1 in
       fun env -> valuec (let c = deepcompare t (f1 env) (f2 env) in
                          match op with
                          | Eq  -> c=0
                          | Neq -> c<>0
                          | Lt  -> c<0
                          | Leq -> c<=0
                          | Geq -> c>=0
                          | Gt  -> c>0
                         )
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
       fun env -> valuec (f (boolc (f1 env)) (boolc (f2 env)))
      )
  | ESub (e1,e2)            ->
      (let f1 = listc <.> compile_expr e1 in
       let f2 = nonnegintc e2.pos "subscript" <.> compile_expr e2 in
       fun env -> valuec (try List.nth (f1 env) (f2 env)
                          with _ -> raise (Error (e.pos, Printf.sprintf "subscript %d not in range of qbits collection length %d"
                                                                    (f2 env)
                                                                    (List.length (f1 env))
                                                 )
                                          )
                         )
      )
  | EMatch  _ (*of expr * ematch list*)
  | ELambda _ (*of pattern list * expr*)
  | EWhere  _ (*of expr * edecl*)
                            -> raise (CompileError(e.pos, Printf.sprintf "can't (yet) compile %s" (string_of_expr e)))

module CExprH = struct type t = expr 
                       let equal = (==) (* yes, identity, not equality *)
                       let hash = Hashtbl.hash
                       let to_string = string_of_expr
                end
module CExprHash = MyHash.Make (CExprH)

let compiletab = CExprHash.create 1000

let compile_expr = CExprHash.memofun compiletab compile_expr
