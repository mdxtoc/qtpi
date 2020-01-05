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
open Process
open Param
open Step
open Def
open Value

open Monenv (* do this last so we get the weird execution environment mechanism *)

exception Error of sourcepos * string

let mon_name pn tpnum = "#mon#" ^ pn.inst.tinst ^ "#" ^ tpnum

let chan_name tpnum = "#chan#" ^ tpnum

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
  let rec cmp proc =
    let ad = adorn proc.pos in
    let adio = adorn proc.pos in
    let ade = tadorn proc.pos in
    match proc.inst with
    | Terminate         -> Some (ad (GSum [adio (Write (ade (EVar (chan_name tpnum)), ade EUnit)), proc]))
    | GSum iops         -> let ciop (iostep, proc) = 
                             match iostep.inst with
                             | Write (ce,_) -> if not (Type.is_classical (type_of_expr ce)) then
                                                 bad iostep.pos "non-classical channel";
                                               Process.optmap cmp proc 
                                               &~~ (_Some <.> (fun proc -> iostep, proc))
                             | _            -> bad iostep.pos "message receive"
                           in
                           Optionutils.optmap_any ciop iops &~~ (_Some <.> ad <.> _GSum) 
    | GoOnAs _      -> bad proc.pos "process invocation"
    | WithQbit _    -> bad proc.pos "qbit creation"
    | WithQstep _   -> bad proc.pos "qbit gating/measuring"
    | WithProc _    -> bad proc.pos "process definition"
    | TestPoint _   -> bad proc.pos "test point"
    | Iter _        -> raise (Error (proc.pos, "Can't compile Iter in compile_monbody yet"))
    | Par _         -> bad proc.pos "parallel sum"
    | WithNew _     
    | WithLet _
    | Cond    _
    | PMatch  _     -> None
  in
  Process.map cmp proc
  
let compile_proc er env pn mon proc =
  let rec cmp proc =
    let ad = adorn proc.pos in
    let ade = tadorn proc.pos in
    let adpat = Pattern.patadorn proc.pos None in
    let adpar = tadorn proc.pos in
    let adn = tadorn proc.pos in
    match proc.inst with
      | TestPoint (tpn, p) -> let p = Process.map cmp p in
                              let read = adorn tpn.pos (Read (ade (EVar (chan_name tpn.inst)), adpat PatAny)) in
                              let gsum = ad (GSum [(read, p)]) in
                              let mn = mon_name pn tpn.inst in
                              let call = ad (GoOnAs (adn mn, [])) in
                              let par = ad (Par [call; gsum]) in
                              let (_, monproc) = _The (find_monel tpn.inst mon) in
                              let def = ad (WithProc ((false, adn mn, [], compile_monbody tpn.inst monproc), par)) in
                              let mkchan = ad (WithNew ([adpar (chan_name tpn.inst)], def)) in
                              Some mkchan
      | WithProc  ((brec,pn,params,proc),p) 
                           -> let p = Process.map cmp p in
                              let proc = Process.map cmp proc in
                              Some (ad (WithProc ((brec,pn,params,proc),p)))
      | Terminate 
      | GoOnAs    _      
      | WithNew   _
      | WithQbit  _
      | WithLet   _
      | WithQstep _
      | Cond      _
      | PMatch    _
      | GSum      _
      | Par       _        -> None
      | Iter _             -> raise (Error (proc.pos, "Can't compile Iter in compile_proc yet"))
  in
  env, Process.map cmp proc

(* I think this should be in Interpret, but then I think it should be here, but then ... *)
let bind_pdef er env (pn,params,p,mon as pdef) =
  let pnum = Monenv.count pn.inst.tinst env in
  let pn' = if pnum=0 then pn 
            else {pn with inst = {pn.inst with tinst = pn.inst.tinst ^ "#" ^ string_of_int (pnum-1)}} 
  in
  let env, proc = compile_proc er env pn' mon p in
  if (!verbose || !verbose_compile) && p<>proc then
    Printf.printf "Compiling .....\n%s....... =>\n%s\n.........\n\n"
                    (string_of_pdef pdef)
                    (string_of_process proc);
  env <@+> (pn.inst.tinst, VProcess (er, names_of_params params, proc))

let compile_builtin (pn,params,p,mon as pdef) =
  if !verbose || !verbose_compile then
    Printf.printf "compiling built-in %s\n" (string_of_pdef pdef);
  if not (null mon) then
    raise (Settings.Error (Printf.sprintf "built_in %s has logging sub-processes" (string_of_typedname pn)));
  (* all we do is append a # to the name ... *)
  let pname = tinst pn in
  ()

