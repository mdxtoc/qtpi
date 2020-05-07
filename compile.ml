(*
    Copyright (C) 2018-2020 Richard Bornat
     
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
open Tupleutils
open Sourcepos
open Instance
open Type
open Name
open Expr
open Pattern
open Cbasics
open Process
open Cprocess
open Param
open Step
open Cstep
open Def
open Monenv 
open Value

open Number
open Snum
open Vmg
open Vt


exception CompileError of sourcepos * string
exception ExecutionError of sourcepos * string

type ctenv = int * name list    (* int is maxextent of environment *)

let (<+>) ctenv name =
  let n, names = ctenv in
  max n (List.length names + 1), name::names
  
let string_of_ctenv = bracketed_string_of_pair string_of_int (bracketed_string_of_list string_of_name)

  let (<?>) (n, names as ctenv) (pos,name) = 
  let tail = dropwhile ((<>)name) names in
  match tail with
  | [] -> raise (CompileError (pos, Printf.sprintf ("%s not in ctenv %s") (string_of_name name) (string_of_ctenv ctenv)))
  | _  -> List.length tail - 1

let tidemark (n,names) (n',_) = max n n', names

(* ************************ compiling matches into functions ************************ *)

(* compile_match works with right-hand sides. It gives you back a tide-marked version of the ctenv you gave it *)
let rec compile_match : sourcepos -> ('a -> string) -> 
                        (ctenv -> 'a -> ctenv * (rtenv -> 'b)) -> 
                        ctenv -> 
                        (pattern * 'a) list -> 
                        ctenv * (rtenv -> vt -> 'b) = 
  fun pos string_of_a compile_a ctenv pairs ->
  
    if !verbose || !verbose_compile then
      (let dtree = Matchcheck.match_dtree false string_of_a pairs in
       Printf.printf "matcher %s %s %s\ndtree (which we're not yet using) = %s\n\n\n" 
                      (string_of_sourcepos pos)
                      (string_of_ctenv ctenv)
                      (Matchcheck.string_of_rules string_of_a pairs)
                      (Matchcheck.string_of_dtree string_of_a dtree)
      ); 
  
   (* this is not a clever way of doing it, but it does avoid the cost of interpretation. I think that's a cost. *)
   let rec dopat : ctenv -> pattern -> ctenv * ((rtenv -> 'b ) -> (unit -> 'b) -> rtenv -> vt -> 'b) = fun ctenv pat ->
     match tinst pat with
     | PatAny            
     | PatUnit           -> ctenv, fun yes no rtenv _ -> yes rtenv 
     | PatNil            -> ctenv, fun yes no rtenv v -> if to_list v=[] then yes rtenv else no ()
     | PatName   n       -> let ctenv = ctenv<+>n in
                            let i = ctenv<?>(pat.pos, n) in
                            ctenv, fun yes no rtenv v -> rtenv.(i)<-v; yes rtenv
     | PatInt    i       -> ctenv, fun yes no rtenv v -> let n = to_num v in if is_int n && num_of_int i =/ n then yes rtenv else no ()
     | PatBit    b       -> ctenv, fun yes no rtenv v -> let b' = to_bit v in if b=b' then yes rtenv else no ()
     | PatBool   b       -> ctenv, fun yes no rtenv v -> let b' = to_bool v in if b=b' then yes rtenv else no ()
     | PatChar   c       -> ctenv, fun yes no rtenv v -> let c' = to_uchar v in if c=c' then yes rtenv else no ()
     | PatString ucs     -> ctenv, fun yes no rtenv v -> let ucs' = to_uchars v in if ucs=ucs' then yes rtenv else no ()
     | PatBra    b       -> ctenv, fun yes no rtenv v -> let b' = to_bra v in if nv_of_braket b=b' then yes rtenv else no ()
     | PatKet    k       -> ctenv, fun yes no rtenv v -> let k' = to_ket v in if nv_of_braket k=k' then yes rtenv else no ()
     | PatCons   (ph,pt) -> let ctenv, fh = dopat ctenv ph in
                            let ctenv, ft = dopat ctenv pt in
                            ctenv, (fun yes no rtenv v ->
                                      match to_list v with
                                      | hd::tl -> fh (fun rtenv -> ft yes no rtenv (of_list tl)) no rtenv hd 
                                      | _      -> no ()
                                   )
     | PatTuple  ps      -> (* the hidden value of a tuple is a vt list *)
                            let rec dotuple : ctenv -> pattern list -> ctenv * ((rtenv -> 'b ) -> (unit -> 'b) -> rtenv -> vt -> 'b) = 
                              fun ctenv -> 
                                function         
                                | p::ps -> let ctenv, fh = dopat ctenv p in
                                           let ctenv, ft = dotuple ctenv ps in
                                           ctenv, fun yes no rtenv v -> let vs = to_list v in 
                                                                        fh (fun rtenv -> ft yes no rtenv (of_list (List.tl vs)))
                                                                           no rtenv (List.hd vs) 
                                | _     -> ctenv, fun yes no rtenv _ -> yes rtenv
                              in
                              dotuple ctenv ps
   in
   let mfail = ExecutionError (pos, "match failure") in
   let rec dopairs : ctenv -> (pattern * 'a) list -> ctenv * (rtenv -> vt -> 'b) = 
     fun ctenv -> 
       function
       | (pat, rhs)::pairs -> let ctenvp, fh = dopat ctenv pat in
                              let ctenvr, frhs = compile_a ctenvp rhs in
                              let ctenv = tidemark ctenv ctenvr in
                              let ctenv, ft = dopairs ctenv pairs in
                              ctenv, fun rtenv v -> fh frhs (fun () -> ft rtenv v) rtenv v
       | []                -> ctenv, fun rtenv v -> raise mfail
   in
   dopairs ctenv pairs
;;

(* temptation to do this with compile_match resisted. This is just an environment exercise, no failure possible. 
   And it gives you back the ctenv of the pattern-match, as well as the pattern compilation. No tidemarking, no rhs compilation.
 *)
let rec compile_bmatch :  ctenv -> pattern -> ctenv * ((rtenv -> 'b) -> (rtenv -> vt -> 'b)) = 
  fun ctenv pat ->
    if !verbose || !verbose_compile then
      Printf.printf "compile_bmatch %s\n" (string_of_pattern pat);
    (* this just to avoid repetitive diagnostic printing *)
    let rec dopat : ctenv -> pattern -> ctenv * ((rtenv -> 'b) -> (rtenv -> vt -> 'b)) = fun ctenv pat ->
      match tinst pat with
      | PatAny            
      | PatUnit           -> ctenv, fun yes rtenv _ -> yes rtenv 
      | PatName   n       -> let ctenv = ctenv<+>n in
                             let i = ctenv<?>(pat.pos,n) in
                             ctenv, fun yes rtenv v -> rtenv.(i)<-v; yes rtenv
      | PatTuple  ps      -> (* the hidden value of a tuple is a vt list *)
                             let rec dotuple : ctenv -> pattern list -> ctenv * ((rtenv -> 'b ) -> rtenv -> vt -> 'b) = 
                               fun ctenv -> 
                                 function         
                                 | p::ps -> let ctenv, fh = dopat ctenv p in
                                            let ctenv, ft = dotuple ctenv ps in
                                            ctenv, fun yes rtenv v -> let vs = to_list v in 
                                                                      fh (fun rtenv -> ft yes rtenv (of_list (List.tl vs)))
                                                                         rtenv (List.hd vs) 
                                 | _     -> ctenv, fun yes rtenv _ -> yes rtenv
                             in
                             dotuple ctenv ps
      | _                 -> raise (Can'tHappen (Printf.sprintf "%s: compile_bmatch %s" (string_of_sourcepos pat.pos)
                                                                                        (string_of_pattern pat)
                                                )
                                   )
    in dopat ctenv pat 
;;

(* ************************ compiling typed expressions into functions ************************ *)

(** Because we have nums in values we can't even use equality, I think.

    Comparison.  [compare x y] returns 0 if [x] equals [y],
    -1 if [x] is smaller than [y], and 1 if [x] is greater than [y].

    Note that Pervasive.compare can be used to compare reliably two integers
    only on OCaml 3.12.1 and later versions.
 *)

let rec deepcompare : _type -> vt -> vt -> int = fun t v1 v2 -> 
  let r = match t.inst with (* list everything to be sure I don't make a mistake *)
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
  in
  r
  
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

let cconst : vt -> rtenv -> vt = fun v rtenv -> v
;;

let rec compile_expr : ctenv -> expr -> ctenv * (rtenv -> vt) = fun ctenv e ->
  if !verbose || !verbose_compile then
    (Printf.printf "compile_expr %s %s\n" (string_of_ctenv ctenv) (string_of_expr e); flush_all());
  
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
  | EUnit           -> ctenv, cconst (of_unit ())
  | EVar n          -> let i = ctenv<?>(e.pos, n) in
                       ctenv, fun rtenv -> rtenv.(i) 
  | ENum num        -> ctenv, cconst (of_num num)
  | EBool b         -> ctenv, cconst (of_bool b)
  | EChar uc        -> ctenv, cconst (of_uchar uc)
  | EString ucs     -> ctenv, cconst (of_uchars ucs)
  | EBit b          -> ctenv, cconst (of_bit b)
  | EBra b          -> ctenv, cconst (of_nv (nv_of_braket b))
  | EKet k          -> ctenv, cconst (of_nv (nv_of_braket k))
  | EMinus e        -> (* overloaded *)
      (let ctenv, f = compile_expr ctenv e in
       match et.inst with
       | Num   -> ctenv, fun rtenv -> of_num (~-/(to_num (f rtenv)))
       | Sxnum -> ctenv, fun rtenv -> of_csnum (Snum.cneg (to_csnum (f rtenv)))
       | _     -> can'thappen ()
      )
  | ENot e          ->
      let ctenv, f = compile_expr ctenv e in
      ctenv, fun rtenv -> of_bool (not (to_bool (f rtenv)))
  | EDagger e       -> (* overloaded *)
      (let ctenv, f = compile_expr ctenv e in
       match et.inst with
       | Gate   -> ctenv, fun rtenv -> of_gate (dagger_g (to_gate (f rtenv)))
       | Matrix -> ctenv, fun rtenv -> of_matrix (dagger_m (to_matrix (f rtenv)))
       | _      -> can'thappen ()
      )
  | ETuple es       ->
      let apply rtenv f = f rtenv in
      let compile (ctenv,fs) e = 
        let ctenv,f = compile_expr ctenv e in
        ctenv, f::fs
      in
      let ctenv, fs = List.fold_left compile (ctenv,[]) es in
      ctenv, fun rtenv -> of_tuple (List.map (apply rtenv) fs)
  | ENil        -> ctenv, cconst (of_list [])
  | ERes w      -> 
      (match et.inst with
       | Fun (t,_) ->
           (match w with
            | ResShow -> 
                let optf t = match t.inst with
                                     | Qbits     -> Some "<qbit>"
                                     | Qstate    -> Some "<qstate>"
                                     | Fun     _ -> Some "<function>"
                                     | Channel _ -> Some "<channel>"
                                     | Process _ -> Some "<process>"
                                     | Unknown _       
                                     | Known   _         
                                     | Poly    _ -> Some (string_of_value t (of_unit ()))
                                     | _         -> None
                in
                (match optf t with
                 | Some s -> warning e.pos (Printf.sprintf "applied to a value of type %s, 'show' can only print \"%s\"" 
                                                                (string_of_type t) s
                                           )
                 | None   -> if is_polytype t then
                                warning e.pos (Printf.sprintf "'show' used with poly-type %s"  (string_of_type et))
                );
                
                let f = so_value optf t in
                ctenv, fun rtenv -> of_fun (hide_string <.> f)
            | ResCompare ->
                if is_polytype t then
                  raise (CompileError (e.pos, Printf.sprintf "'compare' used with poly-type %s" 
                                                                    (string_of_type et)
                                      )
                         );
                 let f = deepcompare t in
                 ctenv, fun rtenv -> of_fun (fun v -> of_fun (fun v' -> hide_int (f v v')))
           )
       | _         -> raise (Can'tHappen (Printf.sprintf "%s %s" (string_of_expr e) (string_of_type et)))
      )
  | ECons (e1,e2)   ->
      let ctenv, f1 = compile_expr ctenv e1 in
      let ctenv, f2 = compile_expr ctenv e2 in
      ctenv, fun rtenv -> of_list (f1 rtenv :: (to_list (f2 rtenv)))
  | EAppend (e1,e2)     ->
      let ctenv, f1 = compile_expr ctenv e1 in
      let ctenv, f2 = compile_expr ctenv e2 in
      ctenv, fun rtenv -> of_list (List.append (to_list (f1 rtenv)) (to_list (f2 rtenv)))
  | ECond (ce,te,ee)    ->
      let ctenv, cf = compile_expr ctenv ce in
      let ctenv, tf = compile_expr ctenv te in
      let ctenv, ef = compile_expr ctenv ee in
      ctenv, fun rtenv -> (if (to_bool (cf rtenv)) then tf else ef) rtenv
  | EJux (fe,ae)        ->
      let ctenv, ff = compile_expr ctenv fe in
      let ctenv, af = compile_expr ctenv ae in
      ctenv, (fun rtenv -> try (to_fun (ff rtenv)) (af rtenv)
                           with LibraryError s -> raise (ExecutionError (e.pos, s))
             )
    
  | EArith (e1,op,e2)  ->
      let ctenv, f1 = compile_expr ctenv e1 in
      let ctenv, f2 = compile_expr ctenv e2 in
      ctenv, (match op with
              | Plus            
              | Minus      ->
                  (match (type_of_expr e1).inst with
                   | Num    -> let f = if op=Plus then (+/) else (-/) in
                               fun rtenv -> of_num (f (to_num (f1 rtenv)) (to_num (f2 rtenv)))
                   | Matrix -> let f = if op=Plus then add_mm else sub_mm in
                               fun rtenv -> of_matrix (f (to_matrix (f1 rtenv)) (to_matrix (f2 rtenv)))
                   | Sxnum  -> let f = if op=Plus then Snum.csum else Snum.cdiff in
                               fun rtenv -> of_csnum (f (to_csnum (f1 rtenv)) (to_csnum (f2 rtenv)))
                   | _      -> can'thappen ()
                  )
              | Times      ->
                  (match (type_of_expr e1).inst, (type_of_expr e2).inst with
                   | Num   , Num    -> fun rtenv -> of_num ((to_num (f1 rtenv)) */ (to_num (f2 rtenv)))
                   | Sxnum , Sxnum  -> fun rtenv -> of_csnum (cprod (to_csnum (f1 rtenv)) (to_csnum (f2 rtenv)))
                   | Gate  , Gate   -> fun rtenv -> of_gate (mult_gg (to_gate (f1 rtenv)) (to_gate (f2 rtenv)))
                   | Ket   , Bra    -> fun rtenv -> of_matrix (mult_kb (to_ket (f1 rtenv)) (to_bra (f2 rtenv)))
                   | Matrix, Matrix -> fun rtenv -> of_matrix (mult_mm (to_matrix (f1 rtenv)) (to_matrix (f2 rtenv)))
                   | Sxnum , Matrix -> fun rtenv -> of_matrix (mult_nm (to_csnum (f1 rtenv)) (to_matrix (f2 rtenv)))
                   | Matrix, Sxnum  -> fun rtenv -> of_matrix (mult_nm (to_csnum (f2 rtenv)) (to_matrix (f1 rtenv)))
                   | _                         -> can'thappen()
                  )
              | Div        -> fun rtenv -> of_num (to_num (f1 rtenv) // to_num (f2 rtenv))
              | Power      -> fun rtenv -> of_num (to_num (f1 rtenv) **/ intc e2.pos "fractional power" (f2 rtenv))
              | Mod        -> fun rtenv -> let n1 = to_num (f1 rtenv) in
                                         let n2 = to_num (f2 rtenv) in
                                         if is_int n1 && is_int n2 then
                                           of_num (rem n1 n2)
                                         else 
                                           raise (ExecutionError (e.pos, Printf.sprintf "fractional remainder %s %s" 
                                                                                           (string_of_num n1)
                                                                                           (string_of_num n2)
                                                                 )
                                                 )
              | TensorProd -> (* overloaded *)
                  (match (type_of_expr e1).inst with
                   | Gate   -> fun rtenv -> of_gate (tensor_gg (to_gate (f1 rtenv)) (to_gate (f2 rtenv)))
                   | Bra  
                   | Ket    -> fun rtenv -> of_nv (tensor_nvnv (to_nv (f1 rtenv)) (to_nv (f2 rtenv)))
                   | Matrix -> fun rtenv -> of_matrix (tensor_mm (to_matrix (f1 rtenv)) (to_matrix (f2 rtenv)))
                   | _      -> can'thappen()
                  )
              | TensorPower ->
                  (let powc = nonnegintc e2.pos "tensor-power exponent" in
                   match (type_of_expr e1).inst with
                   | Gate   -> fun rtenv -> of_gate (tensorpow_g (to_gate (f1 rtenv)) (powc (f2 rtenv)))
                   | Bra    
                   | Ket    -> fun rtenv -> of_nv (tensorpow_nv (to_nv (f1 rtenv)) (powc (f2 rtenv)))
                   | Matrix -> fun rtenv -> of_matrix (tensorpow_m (to_matrix (f1 rtenv)) (powc (f2 rtenv)))
                   | _      -> can'thappen()
                  )
              )
  | ECompare (e1,op,e2) ->
      let ctenv, f1 = compile_expr ctenv e1 in
      let ctenv, f2 = compile_expr ctenv e2 in
      let t = type_of_expr e1 in
      let tricky f = 
        if is_polytype t then
          raise (CompileError (e.pos, (Printf.sprintf "'%s' used with poly-type %s->%s->bool" 
                                                            (string_of_compareop op)
                                                            (string_of_type (type_of_expr e1))
                                                            (string_of_type (type_of_expr e2))
                                        )
                                )
                 )
        else f <..> deepcompare t
      in
      let cf = match op with
               | Eq  -> (=)
               | Neq -> (<>)
               | Lt  -> tricky ((>)0) 
               | Leq -> tricky ((>=)0)
               | Geq -> tricky ((<=)0)
               | Gt  -> tricky ((<)0) 
      in
      ctenv, fun rtenv -> of_bool (cf (f1 rtenv) (f2 rtenv))
  | EBoolArith (e1,op,e2)   ->
      let ctenv, f1 = compile_expr ctenv e1 in
      let ctenv, f2 = compile_expr ctenv e2 in
      let f = match op with
              | And       -> (&&)
              | Or        -> (||)
              | Implies   -> (fun b1 b2 -> (not b1) || b2)
              | Iff       -> (=)
      in
      ctenv, fun rtenv -> of_bool (f (to_bool (f1 rtenv)) (to_bool (f2 rtenv)))
  | ESub (e1,e2)            ->
       let ctenv, f1 = compile_expr ctenv e1 in
       let ctenv, f2 = compile_expr ctenv e2 in 
       ctenv, fun rtenv -> let qs = to_list (f1 rtenv) in
                           let i = nonnegintc e2.pos "subscript" (f2 rtenv) in
                           (try List.nth qs i 
                            with _ -> raise (ExecutionError (e.pos, Printf.sprintf "subscript %d not in range of qbits collection length %d"
                                                                      i
                                                                      (List.length qs)
                                                   )
                                            )
                           )
  | EMatch  (me,ems)     -> let ctenv, fe = compile_expr ctenv me in
                            let ctenv', fm = compile_match e.pos string_of_expr compile_expr ctenv ems in
                            tidemark ctenv ctenv', fun rtenv -> fm rtenv (fe rtenv)
  | ELambda (pats, le)   -> let f = compile_fun e.pos (Expr.frees e) ctenv pats le in
                            ctenv, hide_fun f
  | EWhere  (be, ed)     -> (match ed.inst with
                             | EDPat (pat,_,we) ->
                                 let ctenv, wef = compile_expr ctenv we in
                                 let ctenvp, pf = compile_bmatch ctenv pat in
                                 let ctenve, ef = compile_expr ctenvp be in
                                 tidemark ctenv ctenve, fun rtenv -> pf ef rtenv (wef rtenv)
                             | EDFun (fn,pats,_, we) ->
                                 let ctenvw = ctenv<+>tinst fn in
                                 let ff = compile_fun we.pos (Expr.frees we) ctenvw pats we in
                                 let ctenve, ef = compile_expr ctenvw be in
                                 let i = ctenvw<?>(ed.pos,tinst fn) in
                                 tidemark ctenv ctenve, fun rtenv -> rtenv.(i)<-of_fun (ff rtenv); ef rtenv
                            )

(* gives back something which, from an environment, makes a function ... 
   We don't give it a ctenv, and the returned ctenv is the one for the lambda
 *)  
and compile_fun : sourcepos -> NameSet.t -> ctenv -> pattern list -> expr -> (rtenv -> vt -> vt) = 
  fun pos frees ctenv pats expr ->
    let rec cl : ctenv -> pattern list -> ctenv * (rtenv -> vt -> vt) =
      fun ctenv ->
        function
        | [pat]     -> let ctenvp, pf = compile_bmatch ctenv pat in
                       let ctenve, ef = compile_expr ctenvp expr in
                       tidemark ctenv ctenve, pf ef
        | pat::pats -> let ctenvp, pf = compile_bmatch ctenv pat in
                       let ctenvt, ff = cl ctenvp pats in
                       tidemark ctenv ctenvt, pf (hide_fun ff) 
        | []        -> raise (Can'tHappen "compile_fun.cl")
    in
    let frees = NameSet.elements frees in
    let ctenvl = List.length frees, frees in
    let ctenvl, lf = cl ctenvl pats in (* we need the tidemark *)
    let addpos name = pos,name in
    let pairs = List.map (fun f -> ctenvl<?>(pos,f), ctenv<?>(pos,f)) frees in
    let mkenv rtenv = 
      let rtenv' = Array.make (fst ctenvl) (of_unit ()) in
      List.iter (fun (i',i) -> rtenv'.(i') <- rtenv.(i)) pairs;
      rtenv'
    in
    fun rtenv v -> let rtenv' = mkenv rtenv in lf rtenv' v (* delay the new-environment creation, for the sake of recursive functions *)

and hide_fun : (rtenv -> vt -> vt) -> (rtenv -> vt) = Obj.magic
  
(* ************************ compiling processes ************************ *)

let env_cpat pat = compile_bmatch pat Functionutils.id

let cexpr_opt eopt = eopt &~~ (_Some <.> compile_expr)

let rec compile_proc : process -> cprocess = fun proc ->
  let adorn = adorn proc.pos in
  match proc.inst with
  | Terminate           -> adorn CTerminate
  | GoOnAs (pn, es)     -> adorn (CGoOnAs (pn, List.map compile_expr es))             (* GoOnAs: homage to Laski *)
  | WithNew (bps, contn) 
                        -> adorn (CWithNew (bps, compile_proc contn))
  | WithQbit (plural, qspecs, contn)
                        -> adorn (CWithQbit (plural, List.map compile_qspec qspecs, compile_proc contn))
  | WithLet (lsc, contn) 
                        -> adorn (CWithLet (compile_letspec lsc, compile_proc contn))
  | WithProc ((brec,pn',params,proc'),contn)
                        -> adorn (CWithProc ((brec,pn',params,compile_proc proc'), compile_proc contn))
  | WithQstep (qstep, contn)
                        -> adorn (CWithQstep (compile_qstep qstep, compile_proc contn))
  | JoinQs (ns, p, contn)
                        -> adorn (CJoinQs (ns, p, compile_proc contn))
  | SplitQs (n, splitspecs, contn)
                        -> adorn (CSplitQs (n, List.map compile_splitspec splitspecs, compile_proc contn))
  | TestPoint _         -> raise (CompileError (steppos proc, "TestPoint not precompiled"))
  | Iter _              -> raise (CompileError (steppos proc, "Iter not precompiled"))
  | Cond (e, proct, procf)
                        -> adorn (CCond (compile_expr e, compile_proc proct, compile_proc procf))
  | PMatch (e, pms)     -> let compile_pm contn =
                             let ccontn = compile_proc contn in
                             fun rtenv -> rtenv, ccontn
                           in 
                           let fcpm = compile_match (steppos proc) string_of_process compile_pm pms in
                           adorn (CPMatch (compile_expr e, fcpm))
  | GSum ioprocs        -> adorn (CGSum (List.map compile_ioproc ioprocs))
  | Par procs           -> adorn (CPar (List.map compile_proc procs))
  
and compile_qspec (p, eopt) = p, cexpr_opt eopt

and compile_letspec (pat, e) = env_cpat pat, compile_expr e

and compile_qstep qstep =
  let adorn = adorn qstep.pos in
  match qstep.inst with
  | Measure (plural, qe, geopt, pat)    ->
      adorn (CMeasure (plural, compile_expr qe, cexpr_opt geopt, env_cpat pat))
  | Through (plural, qes, ge)           ->
      adorn (CThrough (plural, List.map compile_expr qes, compile_expr ge))

and compile_splitspec (p, eopt) = p, cexpr_opt eopt

and compile_ioproc (iostep, contn) =
  let ccontn = compile_proc contn in
  let adorn = adorn iostep.pos in
  match iostep.inst with
  | Read (ce,pat)   -> adorn (CRead (compile_expr ce, type_of_pattern pat, env_cpat pat)), ccontn
  | Write (ce,e)    -> adorn (CWrite (compile_expr ce, type_of_expr e, compile_expr e)), ccontn

(* ************************ compiling sub-processes ************************ *)

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

let precompile_proc ctenv pn mon proc =
  (* if !verbose || !verbose_compile then
       Printf.printf "precompile_proc ctenv=%s\n  pn=%s\n  mon=(%s)\n proc=(%s)\n"
                       (string_of_env ctenv)
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
  ctenv, Process.map (cmp (steppos proc)) proc

(* I think this should be in Interpret, but then I think it should be here, but then ... *)
let bind_pdef er ctenv (pn,params,p,mon as pdef) =
  let ctenv, proc = precompile_proc ctenv pn mon p in
  if (!verbose || !verbose_compile) && p<>proc then
    Printf.printf "Expanding .....\n%s....... =>\n%s\n.........\n\n"
                    (string_of_pdef pdef)
                    (string_of_process proc);
  ctenv <@+> (tinst pn, of_procv (tinst pn, er, names_of_params params, compile_proc proc))

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
  let assoc = Typecheck.typecheck_pdefs [] [pdef'] in
  Typecheck.rewrite_pdef pdef';
  assoc <@> pname', pdef'

