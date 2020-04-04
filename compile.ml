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

open Monenv (* do this last so we get the weird execution environment mechanism *)

exception Error of sourcepos * string

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
    | JoinQs _      -> bad proc.pos "qbits joining"
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


