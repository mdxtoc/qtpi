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
exception Disaster of sourcepos * string

(* ctenv type has changed, because Par needs more careful treatment. 
   nx: next free slot
   hw: highwater mark
   slots: assoc list
 *)
 
type ctenv = { nx: int; hw: int; slots: (name*int) list}    

let string_of_ctenv ctenv = 
  Printf.sprintf "{nx=%d;hw=%d;slots=(%s)}" 
       ctenv.nx ctenv.hw
       (string_of_assoc string_of_name string_of_int ":" ";" ctenv.slots)

let empty_ctenv = {nx=0;hw=0;slots=[]}

let (<+>) {nx=nx;hw=hw;slots=slots} name =
  {nx=nx+1; hw=Stdlib.max hw (nx+1); slots=(name,nx)::slots} 
  
let (<?>) ctenv (pos,name) = 
  try ctenv.slots <@> name 
  with Not_found ->
    raise (CompileError (pos, Printf.sprintf "%s not in ctenv %s" (string_of_name name) (string_of_ctenv ctenv)))

let (<+?>) ctenv name =
  let ctenv = ctenv<+> name in
  ctenv, ctenv<?>(dummy_spos,name)

(* reverse lookup *)
let (<-?>) ctenv (pos,i) =
  try invassoc ctenv.slots i
  with Not_found -> raise (CompileError (pos, Printf.sprintf "%s<-?>%d" (string_of_ctenv ctenv) i))

let tidemark ctenv ctenv' = {ctenv with hw=max ctenv.hw ctenv'.hw}

let add_ctnames = List.fold_left (<+>)

type 'a rtfun = rtenv -> 'a
type 'a rtpatfun = rtenv -> vt -> 'a

(* the compile argument to compile_multi must do tidemarking, if necessary. Sometimes you want to augment ctenv ... *)
let compile_multi : (ctenv -> 'x -> ctenv * 'r) -> ctenv -> 'x list -> ctenv * 'r list = 
  fun compile_x ctenv xs -> 
    let compile (ctenv,rs) x =
      let ctenv, r = compile_x ctenv x in
      ctenv, r::rs
    in
    let ctenv, revxs = List.fold_left compile (ctenv,[]) xs in
    ctenv, List.rev revxs

(* for tidemarking in the compile argument to compile_multi. And elsewhere, it turns out *)
let tidemark_f : (ctenv -> 'x -> ctenv * 'r) -> ctenv -> 'x -> ctenv * 'r =
  fun compile ctenv x ->
    let ctenv', r = compile ctenv x in
    tidemark ctenv ctenv', r
    
(* but in Par it's different: the next parallel process has to start binding from the tidemark of the previous *)
let tidemark_par : (ctenv -> 'x -> ctenv * 'r) -> ctenv -> 'x -> ctenv * 'r =
  fun compile ctenv x ->
    let ctenv', r = compile {ctenv with hw=ctenv.nx} x in
    {(tidemark ctenv ctenv') with nx=ctenv'.hw}, r
    
let rtenv_init pos n frees ctenv =
  let ctenvl = add_ctnames empty_ctenv frees in
  let pairs = List.map (fun f -> ctenvl<?>(pos,f), ctenv<?>(pos,f)) frees in
  fun rtenv -> 
    let rtenv' = Array.make n (of_unit ()) in
    List.iter (fun (i',i) -> if !verbose || !verbose_interpret then
                               (Printf.printf "%s: rtenv_init initialises %d(%s) with %d(%s)\n" (string_of_sourcepos pos)
                                                                                                i' (ctenvl<-?>(pos,i'))
                                                                                                i (ctenv<-?>(pos,i));
                                flush_all ()
                               );
                             rtenv'.(i') <- rtenv.(i)) pairs;
    rtenv'

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
                            ctenv, fun yes no rtenv v -> if !verbose || !verbose_interpret then 
                                                           (Printf.printf "%s: match pattern initialises %d(%s)\n" (string_of_sourcepos pat.pos)
                                                                                                                   i (string_of_name n);
                                                            flush_all ()
                                                           );
                                                         rtenv.(i)<-v; yes rtenv
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
      Printf.printf "compile_bmatch %s %s %s\n" (string_of_sourcepos pat.pos) (string_of_ctenv ctenv) (string_of_pattern pat);
    (* this just to avoid repetitive diagnostic printing *)
    let rec dopat : ctenv -> pattern -> ctenv * ((rtenv -> 'b) -> (rtenv -> vt -> 'b)) = fun ctenv pat ->
      match tinst pat with
      | PatAny            
      | PatUnit           -> ctenv, fun yes rtenv _ -> yes rtenv 
      | PatName   n       -> let ctenv = ctenv<+>n in
                             let i = ctenv<?>(pat.pos,n) in
                             ctenv, fun yes rtenv v -> if !verbose || !verbose_interpret then 
                                                           (Printf.printf "%s: bmatch pattern initialises %d(%s)\n" (string_of_sourcepos pat.pos)
                                                                                                                    i (string_of_name n);
                                                            flush_all ()
                                                           );
                                                         rtenv.(i)<-v; yes rtenv
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
          | Qubit
          | Qubits     
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

(* does compile_expr do proper tidemarking? I believe so. *)
let rec compile_expr : ctenv -> expr -> ctenv * (rtenv -> vt) = fun ctenv e ->
  if !verbose || !verbose_compile then
    (Printf.printf "compile_expr %s %s %s\n" (string_of_sourcepos e.pos) (string_of_ctenv ctenv) (string_of_expr e); flush_all());
  
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
      let revapply rtenv f = f rtenv in
      let ctenv, fs = compile_exprs ctenv es in
      ctenv, fun rtenv -> of_tuple (List.map (revapply rtenv) fs)
  | ENil        -> ctenv, cconst (of_list [])
  | ERes w      -> 
      (match et.inst with
       | Fun (t,_) ->
           (match w with
            | ResShow -> 
                let optf t = match t.inst with
                                     | Qubits     -> Some "<qubit>"
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
                   | Matrix, Matrix -> fun rtenv -> of_matrix (mult_mm (to_matrix (f1 rtenv)) (to_matrix (f2 rtenv)))
                   | Gate  , Ket    -> fun rtenv -> of_ket (mult_gnv (to_gate (f1 rtenv)) (to_ket (f2 rtenv)))
                   | Ket   , Bra    -> fun rtenv -> of_matrix (mult_kb (to_ket (f1 rtenv)) (to_bra (f2 rtenv)))
                   | Sxnum , Matrix -> fun rtenv -> of_matrix (mult_nm (to_csnum (f1 rtenv)) (to_matrix (f2 rtenv)))
                   | Matrix, Sxnum  -> fun rtenv -> of_matrix (mult_nm (to_csnum (f2 rtenv)) (to_matrix (f1 rtenv)))
                   | _                           -> can'thappen()
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
                            with _ -> raise (ExecutionError (e.pos, Printf.sprintf "subscript %d not in range of qubits collection length %d"
                                                                      i
                                                                      (List.length qs)
                                                   )
                                            )
                           )
  | EMatch  (me,ems)     -> let ctenv, ef = compile_expr ctenv me in
                            let ctenv', fm = compile_match e.pos string_of_expr compile_expr ctenv ems in
                            tidemark ctenv ctenv', fun rtenv -> fm rtenv (ef rtenv)
  | ELambda (pats, le)   -> let f = compile_fun e.pos ctenv pats le in
                            ctenv, hide_fun f
  | EWhere  (be, ed)     -> (match ed.inst with
                             | EDPat (pat,_,we) ->
                                 let ctenv, wef = compile_expr ctenv we in
                                 let ctenvp, pf = compile_bmatch ctenv pat in
                                 let ctenve, ef = compile_expr ctenvp be in
                                 tidemark ctenv ctenve, fun rtenv -> pf ef rtenv (wef rtenv)
                             | EDFun (fn,pats,_, we) ->
                                 let ctenvw = ctenv<+>tinst fn in
                                 let ff = compile_fun we.pos ctenvw pats we in
                                 let ctenve, ef = compile_expr ctenvw be in
                                 let i = ctenvw<?>(ed.pos,tinst fn) in
                                 tidemark ctenv ctenve, 
                                   fun rtenv -> if !verbose || !verbose_interpret then 
                                                  (Printf.printf "%s: EDFun initialises %d(%s)\n" (string_of_sourcepos ed.pos)
                                                                                                  i (string_of_name (tinst fn));
                                                   flush_all ()
                                                  );
                                                rtenv.(i)<-of_fun (ff rtenv); ef rtenv
                            )

and compile_exprs ctenv es = compile_multi (tidemark_f compile_expr) ctenv es (* tidemarking belt and braces *)

(* compile_fun gives back something which, from an environment, makes a function ... 
   It sorts out all its own ctenv stuff.
 *)  
and compile_fun : sourcepos -> ctenv -> pattern list -> expr -> (rtenv -> vt -> vt) = 
  fun pos ctenv pats expr ->
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
    let frees = NameSet.elements (Expr.frees_lambda pats expr) in
    let ctenvl = add_ctnames empty_ctenv frees in
    let ctenvl, lf = cl ctenvl pats in (* we need the tidemark *)
    let mkenv = rtenv_init pos ctenvl.hw frees ctenv in
    fun rtenv v -> let rtenv' = mkenv rtenv in lf rtenv' v (* delay the new-environment creation, for the sake of recursive functions *)

and hide_fun : (rtenv -> vt -> vt) -> (rtenv -> vt) = Obj.magic
  
(* ************************ compiling processes ************************ *)

let env_cpat ctenv pat = 
  let ctenv, f = compile_bmatch ctenv pat in
  ctenv, f Functionutils.id

let cexpr_opt ctenv eopt = 
  match eopt with
  | None   -> ctenv, None
  | Some e -> let ctenv, ef = compile_expr ctenv e in
              ctenv, Some ef

let rec compile_proc : name -> ctenv -> process -> ctenv * cprocess = fun pn ctenv proc ->
  if !verbose || !verbose_compile then
    (Printf.printf "compile_proc %s %s %s %s\n" (string_of_name pn) (string_of_ctenv ctenv) (string_of_sourcepos (steppos proc)) (short_string_of_process proc); flush_all());
    
  let adorn = adorn proc.pos in
  match proc.inst with
  | Terminate           -> ctenv, adorn CTerminate
  | GoOnAs (pn, es)     -> let ctenv, fs = compile_exprs ctenv es in
                           let name = tinst pn in
                           ctenv, adorn (CGoOnAs (ctenv<?>(pn.pos,name), fs))             (* GoOnAs: homage to Laski *)
  | WithNew ((b,ps), contn) 
                        -> let compile_p ctenv param =  
                             let name = name_of_param param in
                             let ctenv = ctenv<+>name in
                             ctenv, ctenv<?>(param.pos,name)
                           in
                           let ctenvps, is = compile_multi compile_p ctenv ps in (* no tidemarking! *)
                           let ctenvc, ccontn = compile_proc pn ctenvps contn in
                           tidemark ctenv ctenvc, adorn (CWithNew ((b,is), ccontn))
  | WithQubit (plural, qspecs, contn)
                        -> let ctenvqs, cqspecs = compile_multi compile_qspec ctenv qspecs in (* no tidemarking! *)
                           let ctenvc, ccontn = compile_proc pn ctenvqs contn in
                           tidemark ctenv ctenvc, adorn (CWithQubit (plural, cqspecs, ccontn))
  | WithLet (lsc, contn) 
                        -> let ctenvl, clsc = compile_letspec ctenv lsc in
                           let ctenvc, ccontn = compile_proc pn ctenvl contn in
                           tidemark ctenv ctenvc, adorn (CWithLet (clsc, ccontn))
  | WithProc ((brec,pn',params,proc' as pdecl),contn)
                        -> let ctenvp = if brec then ctenv<+>tinst pn' else ctenv in
                           let cpdecl = compile_pdecl (steppos proc) pn ctenvp pdecl in
                           let ctenvc, ccontn = compile_proc pn (ctenv<+>tinst pn') contn in
                           tidemark ctenv ctenvc, adorn (CWithProc (ctenvc<?>(steppos proc,tinst pn'), cpdecl, ccontn))
  | WithQstep (qstep, contn)
                        -> let ctenvq, cqstep = compile_qstep ctenv qstep in
                           let ctenvc, ccontn = compile_proc pn ctenvq contn in
                           tidemark ctenv ctenvc, adorn (CWithQstep (cqstep, ccontn))
  | JoinQs (ns, p, contn)
                        -> let is = List.map (fun n -> ctenv<?>(n.pos,tinst n)) ns in
                           let ctenvp = ctenv<+>name_of_param p in 
                           let ctenvc, ccontn = compile_proc pn ctenvp contn in
                           tidemark ctenv ctenvc, adorn (CJoinQs (is, ctenvp<?>(p.pos,name_of_param p), ccontn))
  | SplitQs (n, splitspecs, contn)
                        -> let i = ctenv<?>(n.pos,tinst n) in
                           let ctenvss, csplitspecs = compile_multi compile_splitspec ctenv splitspecs in (* no tidemarking! *)
                           let ctenvc, ccontn = compile_proc pn ctenvss contn in
                           tidemark ctenv ctenvc, adorn (CSplitQs (i, csplitspecs, ccontn))
  | TestPoint _         -> raise (CompileError (steppos proc, "TestPoint not precompiled"))
  | Iter _              -> raise (CompileError (steppos proc, "Iter not precompiled"))
  | Cond (e, proct, procf)
                        -> let ctenv, ef = compile_expr ctenv e in
                           let ctenv, cproct = (tidemark_f (compile_proc pn)) ctenv proct in
                           let ctenvc, cprocf = (tidemark_f (compile_proc pn)) ctenv procf in
                           tidemark ctenv ctenvc, adorn (CCond (ef, cproct, cprocf))
  | PMatch (e, pms)     -> let compile_pm ctenv contn =
                             let ctenv, ccontn = compile_proc pn ctenv contn in
                             ctenv, fun rtenv -> rtenv, ccontn
                           in 
                           let ctenv, fcpm = compile_match (steppos proc) string_of_process (tidemark_f compile_pm) ctenv pms in
                           let ctenvc, ef = compile_expr ctenv e in
                           tidemark ctenv ctenvc, adorn (CPMatch (ef, fcpm))
  | GSum ioprocs        -> let ctenv, cioprocs = compile_multi (tidemark_f (compile_ioproc pn)) ctenv ioprocs in
                           ctenv, adorn (CGSum cioprocs)
  | Par procs           -> let ctenv, cprocs = compile_multi (tidemark_par (compile_proc pn)) ctenv procs in
                           let isCGoOnAs cp = match cp.inst with CGoOnAs _ -> true | _ -> false in
                           let contns = List.filter (not <.> isCGoOnAs) cprocs in
                           ctenv, (match contns with
                                   | [contn] -> adorn (CSpawn (List.filter isCGoOnAs cprocs, contn))
                                   | _       -> adorn (CPar cprocs)
                                  )
  
and compile_qspec ctenv (p, eopt) = 
  let ctenv, ef = match eopt with
                  | Some e -> let ctenv, fe = compile_expr ctenv e in
                              ctenv<+>name_of_param p, Some fe
                  | None   -> ctenv<+>name_of_param p, None
  in
  ctenv, (ctenv<?>(p.pos, name_of_param p), ef)

and compile_letspec ctenv (pat, e) = 
  let ctenv, ef = compile_expr ctenv e in
  let ctenv, envf = env_cpat ctenv pat in 
  ctenv, (envf,ef)

and compile_qstep ctenv qstep =
  let adorn = adorn qstep.pos in
  match qstep.inst with
  | Measure (plural, qe, geopt, pat)    ->
      let ctenv, qf = compile_expr ctenv qe in
      let ctenv, gfopt = cexpr_opt ctenv geopt in
      let ctenv, pf = env_cpat ctenv pat in
      ctenv, adorn (CMeasure (plural, qf, gfopt, pf))
  | Through (plural, qes, ge, unique)           ->
      let ctenv, qfs = compile_multi (tidemark_f compile_expr) ctenv qes in
      let ctenv, gf = compile_expr ctenv ge in
      if false then
        Printf.printf "%s is %s\n" (string_of_qstep qstep) (if !unique then "unique" else "maybe not unique");
      ctenv, adorn (CThrough (plural, qfs, gf, !unique))

and compile_splitspec ctenv (p, eopt) = 
  let ctenv, efopt = cexpr_opt ctenv eopt in
  let ctenvp = ctenv<+>name_of_param p in
  ctenvp, (ctenvp<?>(p.pos,name_of_param p), efopt)

and compile_ioproc pn ctenv (iostep, contn) =
  let adorn = adorn iostep.pos in
  match iostep.inst with
  | Read (ce,pat)   -> let ctenv, cf = compile_expr ctenv ce in
                       let ctenvp, pf = env_cpat ctenv pat in
                       let ctenvc, ccontn = compile_proc pn ctenvp contn in
                       tidemark ctenv ctenvc, (adorn (CRead (cf, type_of_pattern pat, pf)), ccontn)
  | Write (ce,e)    -> let ctenv, cf = compile_expr ctenv ce in
                       let ctenv, ef = compile_expr ctenv e in
                       let ctenvc, ccontn = compile_proc pn ctenv contn in
                       tidemark ctenv ctenvc, (adorn (CWrite (cf, type_of_expr e, ef)), ccontn)

and compile_pdecl pos prefix ctenv (brec,pn,params,proc as pdecl) = (* doesn't return ctenv, because it doesn't bind or evaluate *)
  if !verbose || !verbose_compile then
    (Printf.printf "compile_pdecl %s \"%s\" %s %s\n" (string_of_sourcepos pos)
                                              prefix
                                              (string_of_ctenv ctenv)
                                              (string_of_pdecl pdecl)
    );
  let pn = if prefix="" then (tinst pn) else prefix ^ "_" ^ (tinst pn) in             (* e.g. Alice_⁁1 *)
  let frees = NameSet.elements (pdecl_frees pdecl) in
  let ctenvp = add_ctnames (add_ctnames empty_ctenv frees) (List.map name_of_param params) in
  let ctenvp, cproc = compile_proc pn ctenvp proc in
  let offset = List.length frees in
  let nums = tabulate (List.length params) (fun i -> i+offset) in
  let mkenv = rtenv_init pos ctenvp.hw frees ctenv in
  let airef = ref (0,0) in
  let newpn () = 
    match !airef with
    | 0,0 -> airef := 1,0; pn                                       (* Alice for separate invocation *)
    | a,i -> airef := a+1,i+1; pn ^ "(" ^ string_of_int (i+1) ^ ")"   (* e.g. Alice(2) for simultaneous invocation *)   
    
  in
  let envf = fun rtenv vs -> let rtenv' = mkenv rtenv in
                             if !verbose|| !verbose_interpret then
                               (Printf.printf "ctenvp = %s; nums = %s; vs = %s\n" (string_of_ctenv ctenvp) 
                                                                                  (bracketed_string_of_list string_of_int nums) 
                                                                                  (bracketed_string_of_list string_of_vt vs);
                                flush_all ()
                               );
                             List.iter (fun (i,v) -> if !verbose || !verbose_interpret then
                                                       (Printf.printf "pdecl initialises %d(%s)\n" i (ctenvp<-?>(pos,i));
                                                        flush_all ()
                                                       );
                                                     rtenv'.(i) <- v
                                       ) 
                                       (List.combine nums vs);
                             if !verbose|| !verbose_interpret then (Printf.printf "ok\n"; flush_all ());
                             (newpn(),airef), rtenv', cproc
  in
  pn, envf
  
(* ************************ precompiling sub-processes ************************ *)

let mon_name pn tpnum = "⁁" ^ tpnum

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
    | WithQubit _    
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
    no new qubits (it's outside the protocol, so no quantum stuff)
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
    | WithQubit _   -> bad proc.pos "qubit creation"
    | WithQstep _   -> bad proc.pos "qubit gating/measuring"
    | WithProc _    -> bad proc.pos "process definition"
    | JoinQs _      -> bad proc.pos "joining qubit collections"
    | SplitQs _     -> bad proc.pos "splitting qubit collection"
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
    | TestPoint (tpn, p) -> if !usetestpoints then 
                              let p = Process.map (cmp spos) p in
                              let rc = chan_name tpn.inst in
                              let mn = mon_name pn tpn.inst in
                              let tp = Some (adorn spos (Process [])) in
                              let call = ad (GoOnAs (adn tp mn, [])) in
                              let par = construct_callpar tpn.pos rc call p in
                              let (_, monproc) = _The (find_monel tpn.inst mon) in
                              let def = ad (WithProc ((false, adn tp mn, [], precompile_monbody tpn.inst monproc), par)) in
                              let mkchan = ad (WithNew ((false,[adpar (cut spos) rc]), def)) in
                              Some mkchan
                            else Some (Process.map (cmp spos) p)
    | WithProc  ((brec,pn,params,proc),p) 
                         -> let p = Process.map (cmp spos) p in
                            let proc = Process.map (cmp spos) proc in
                            Some (ad (WithProc ((brec,pn,params,proc),p)))
    | Iter (pat, e, ip, p)
                         -> let p = Process.map (cmp spos) p in
                            let rc = chan_name (short_string_of_sourcepos ip.pos) in
                            let ipname = short_string_of_sourcepos ip.pos in
                            let xname = "x#" in
                            let cname = "c#" in
                            let xtype = type_of_pattern pat in
                            let ctype = _The (cut spos) in
                            let iptype = adorn spos (Process [xtype;ctype]) in
                            let callIter = ad (GoOnAs (adn None "Iter#", [e; ade (Some iptype) (EVar ipname); ade (Some ctype) (EVar rc)])) in
                            let par = construct_callpar ip.pos rc callIter p in
                            let ip = insert_returns true cname ip in
                            let ip = Process.map (cmp spos) ip in
                            let ip = ad (WithLet ((pat, ade (Some xtype) (EVar xname)),ip)) in
                            let def = ad (WithProc ((false, adn (Some iptype) ipname, [adpar (Some xtype) xname; adpar (Some ctype) cname], ip), par)) in
                            let mkchan = ad (WithNew ((false, [adpar (Some ctype) rc]), def)) in
                            Some mkchan
    | Terminate 
    | GoOnAs    _      
    | WithNew   _
    | WithQubit  _
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

