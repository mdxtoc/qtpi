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
open Sourcepos
open Name
open Type
open Listutils
open Optionutils
open Functionutils
open Expr
open Instance
open Processdef
open Param
open Ugate
open Process
open Step

exception TypeUnifyError of _type * _type
exception TypeCheckError of string

type typecxt         = (string * _type) list                  (* use assoc or <@> *)

let string_of_typecxt = 
  string_of_assoc (fun n -> "\n\t" ^ string_of_name n) string_of_type" : " ";"

let new_TypeVar () = TypeVar (new_unknown_name ())

let rec eval cxt n =
  try Some (evaltype cxt (cxt <@> n)) with Not_found -> None

and evaltype cxt t = 
  match t with
  | Int
  | Bool
  | Bit 
  | Unit
  | Qbit            -> t
  | TypeVar n       -> (try evaltype cxt (cxt <@> string_of_name n) with Not_found -> t)
  | Univ (ns,t')    -> let cxt = List.fold_left (fun cxt n -> List.remove_assoc (string_of_name n) cxt) cxt ns in
                       Univ (ns,evaltype cxt t')
  | Range _         -> t
  | List t          -> List (evaltype cxt t)
  | Tuple ts        -> Tuple (List.map (evaltype cxt) ts)
  | Channel t       -> Channel (evaltype cxt t)
  | Fun (t1,t2)     -> Fun (evaltype cxt t1, evaltype cxt t2)
  | Process ts      -> Process (List.map (evaltype cxt) ts)

(* useful in error messages *)
let pickdiff cxt t t1 t2 = 
  let t = evaltype cxt t in
  let t1 = evaltype cxt t1 in
  let t2 = evaltype cxt t2 in
  if t=t1 then t2 else t1
  
let rec unifytype cxt t1 t2 = 
  let t1 = evaltype cxt t1 in
  let t2 = evaltype cxt t2 in
  let exn = TypeUnifyError (t1,t2) in 
  match t1, t2 with
  | TypeVar n1      , TypeVar n2        -> if n1=n2 then cxt else (n1,t2)::cxt
  | TypeVar n1      , _                 -> if canunifytype n1 cxt t2 then (n1,t2)::cxt else raise exn
  | _               , TypeVar n2        -> if canunifytype n2 cxt t1 then (n2,t1)::cxt else raise exn
  | Tuple t1s       , Tuple t2s             
  | Process t1s     , Process t2s       -> unifylists exn cxt t1s t2s 
  | Channel t1      , Channel t2        
  | List t1         , List t2           -> (try unifytype cxt t1 t2 with _ -> raise exn)
  | Fun (t1a,t1b)   , Fun (t2a,t2b)     -> unifylists exn cxt [t1a;t1b] [t2a;t2b]
  | Range (i,j)     , Range (m,n)       -> (* presuming t2 is the context ... *)
                                           if m<=i && j<=n then cxt else raise exn
  | _                                   -> if t1=t2 then cxt else raise exn

and unifypair cxt (t1,t2) = unifytype cxt t1 t2

and unifylists exn cxt t1s t2s = 
  let pairs = try List.combine t1s t2s with Invalid_argument _ -> raise exn in
  List.fold_left unifypair cxt pairs

(* canunify checks that a type doesn't contain TypeVar n *)  
and canunifytype n cxt = function
  | Int
  | Bool
  | Bit 
  | Unit
  | Qbit            
  | Range _         -> true
  | TypeVar n'      -> (match eval cxt n' with
                        | None    -> n<>n'
                        | Some t' -> canunifytype n cxt t'
                       )
  | Process ts       
  | Tuple ts        -> List.for_all (canunifytype n cxt) ts
  | Fun (t1,t2)     -> canunifytype n cxt t1 && canunifytype n cxt t2
  | Channel t      
  | List t          -> canunifytype n cxt t
  | Univ (ns,t)     -> List.mem n ns || canunifytype n cxt t
  
(* when you think you have a complete type context, simplify it with evalcxt. 
   Throws away TypeVars 
 *)
let evalcxt cxt = 
  let evalpair (n,_) = (n, _The (eval cxt n)) in
  let ec = List.map evalpair cxt in
  List.filter (fun (n,_) -> n.[0]<>'?') ec

let string_of_evalcxt = string_of_typecxt <.> evalcxt

let rec assign_name_type pos cxt t n =
  match eval cxt n with
  | Some t' -> 
      let t' = Type.instantiate t' in
      (try unifytype cxt t t' 
       with TypeUnifyError(t1,t2) -> 
         raise (TypeCheckError (n ^ " seems to be type " ^ string_of_type (evaltype cxt t2) ^ 
                                " but in context has to be type " ^ string_of_type (evaltype cxt t1)))
      )
  | None    -> raise (TypeCheckError ("undeclared " ^ string_of_name n ^ " at " ^ string_of_sourcepos pos))

and assigntype_expr cxt t e =
  (* uncurried type_assign_formula *)
  let utaf cxt = uncurry2 (assigntype_expr cxt) in
  try 
    let unary cxt tout tin e = 
       let cxt = unifytype cxt t tout in
       try assigntype_expr cxt tin e 
       with TypeUnifyError (t1,t2) -> 
         raise (TypeCheckError(string_of_expr e ^ 
                    " should be " ^ string_of_type (evaltype cxt tin) ^ 
                    " but is actually " ^ string_of_type (pickdiff cxt tin t1 t2)))
     in
     let binary cxt tout tin1 tin2 f1 f2 =
       let cxt = unary cxt tout tin1 f1 in
       unary cxt tout tin2 f2
     in
     let ternary cxt tout tin1 tin2 tin3 f1 f2 f3 =
       let cxt = binary cxt tout tin1 tin2 f1 f2 in
       unary cxt tout tin3 f3
     in
     match e.inst with
     | EUnit                -> unifytype cxt t Unit
     | EInt i               -> (match evaltype cxt t with 
                                | Bit              -> if i=0||i=1 then cxt
                                                      else unifytype cxt t Int
                                | Range (j,k) as t -> if j<=i && i<=k then cxt 
                                                      else unifytype cxt t Int
                                | t                -> unifytype cxt t Int
                               )
     | EBool _              -> unifytype cxt t Bool
     | EBit b               -> (match evaltype cxt t with 
                                | Int              -> cxt
                                | Range (j,k) as t -> let i = if b then 1 else 0 in
                                                      if j<=i && i<=k then cxt 
                                                      else unifytype cxt t Bit
                                | t                -> unifytype cxt t Bit
                               )
     | EVar n               -> assign_name_type e.pos cxt t n
     | EApp (e1,e2)         -> let atype = new_TypeVar() in
                               let ftype = Fun (atype, t) in
                               let cxt = assigntype_expr cxt ftype e1 in 
                               assigntype_expr cxt atype e2
     | EMinus e             -> unary cxt Int Int  e
     | ETuple es            -> let ts = List.map (fun _ -> new_TypeVar ()) es in
                               let tes = List.combine ts es in
                               let cxt' = List.fold_left utaf cxt tes in
                               unifytype cxt' t (Tuple ts)
     | EList es             -> let t' = new_TypeVar() in
                               let cxt = List.fold_left (fun cxt -> assigntype_expr cxt t') cxt es in
                               unifytype cxt t (List t')
     | ECond (c,e1,e2)      -> ternary cxt t Bool t t c e1 e2
     | EArith (e1,_,e2)     -> binary cxt Int  Int  Int  e1 e2
     | ECompare (e1,op,e2)  -> (match op with 
                                   | Eq | Neq ->
                                       let t = new_TypeVar () in
                                       binary cxt Bool t t e1 e2
                                   | _ ->
                                       binary cxt Bool Int Int  e1 e2
                                  )
     | EBoolArith (e1,_,e2) -> binary cxt Bool  Bool  Bool  e1 e2
     | EAppend (e1,e2)      -> let t' = List (new_TypeVar()) in
                               let cxt = assigntype_expr cxt t' e1 in
                               let cxt = assigntype_expr cxt t' e2 in
                               unifytype cxt t t'
     | EBitCombine (e1, e2) -> let t1 = new_TypeVar () in
                               let cxt = assigntype_expr cxt t1 e1 in
                               let cxt = assigntype_expr cxt Bit e2 in
                               (* if e1 is a Bit, an Int or a Range then we know what to do. 
                                * Otherwise force Int
                                *)
                               (match evaltype cxt t1 with
                                | Int         -> unifytype cxt t Int
                                | Bit         -> unifytype cxt t (Range (0,3))
                                | Range (j,k) -> unifytype cxt t (Range (2*j, 2*k+1))
                                | t1          -> let cxt = unifytype cxt t1 Int in
                                                 unifytype cxt t Int
                               )
with 
  | TypeUnifyError (t1,t2)  -> raise (TypeCheckError (Printf.sprintf "%s appears to be type %s, but in context should be %s"
                                                                     (string_of_expr e) 
                                                                     (string_of_type (evaltype cxt t2))
                                                                     (string_of_type (evaltype cxt t1))
                                                     )
                                     )
  | TypeCheckError s        -> raise (TypeCheckError (Printf.sprintf "%s (in context %s at %s)"
                                                                     s 
                                                                     (string_of_expr e)
                                                                     (string_of_sourcepos e.pos)
                                                     )
                                     )
  
let ok_procname n = 
  let c = Stringutils.first n in
  if not ('A' <= c && c <= 'Z') then raise (TypeCheckError ("process name " ^ string_of_name n ^ " should start with upper case"))

let rec typecheck_ugate cxt ugate = (* arity, cxt *)
  match ugate with
  | GH
  | GI
  | GX          -> 1, cxt
  | GCnot       -> 2, cxt 
  | GPhi (e)    -> 1, assigntype_expr cxt (Range (0,3)) e
  | GCond (e, ug1, ug2)   -> let cxt = assigntype_expr cxt Bool e in
                             let a1, cxt = typecheck_ugate cxt ug1 in
                             let a2, cxt = typecheck_ugate cxt ug2 in
                             if a1=a2 then a1,cxt
                             else raise (TypeCheckError ("arity mismatch in " ^ string_of_ugate ugate))

let strip_procparams s cxt params = 
  (* Printf.printf "before strip_procparams %s (%s)\n%s\n" s (string_of_params params) (string_of_typecxt cxt); *)
  let cxt = List.fold_left (fun cxt (n,_) -> cxt<@->n) cxt params in
  (* Printf.printf "after strip_procparams %s\n" (string_of_typecxt cxt); *)
  cxt

let rec do_procparams s cxt params proc =
  let process_param = function
    | n, None   -> n, new_TypeVar()
    | n, Some t -> n, t
  in
  let cxt = (List.map process_param params) @ cxt in
  let cxt = typecheck_process cxt proc in
  strip_procparams s cxt params

and typecheck_process cxt p =
  match p with
  | Terminate     -> cxt
  | Call (n,args) -> 
      ok_procname n;
      let ts = 
        (try match evaltype cxt (cxt<@>n) with 
             | Process ts -> ts
             | t          -> raise (TypeCheckError (string_of_name n ^ " used as process name, but declared as " ^ string_of_type t))
         with _ -> raise (TypeCheckError ("undefined process " ^ string_of_name n))
        )
      in
      let ets = try zip args ts
                with Zip -> 
                       raise (TypeCheckError (Printf.sprintf "%s: should have %d arguments"
                                                             (string_of_process p)
                                                             (List.length ts)
                                             )
                             )
      in
      List.fold_left (fun cxt (e,t) -> assigntype_expr cxt t e) cxt ets
  | WithNew (params, proc) ->
      (* all the params have to be channels *)
      let cxt, rparams = 
        List.fold_left (fun (cxt, rps) (n, opt) -> 
                          let ct = Channel (new_TypeVar ()) in
                          match opt with 
                          | Some t -> unifytype cxt t ct, ((n, opt)::rps)
                          | None   -> cxt, ((n, Some ct)::rps)           
                       )
                       (cxt, [])
                       params
      in
      do_procparams "WithNew" cxt (List.rev rparams) proc
  | WithQbit (qss,proc) ->
      let params = List.map (fun (n,_) -> n, Some Qbit) qss in
      do_procparams "WithQbit" cxt params proc
  | WithStep (step,proc) ->
      (match step with
       | Read (chan, params) ->
           let chants = List.map (fun _ -> new_TypeVar()) params in 
           let chant = Type.delist chants in
           let cxt = assigntype_expr cxt (Channel chant) chan in
           let stitch s (cxt, params) = 
             match s with
             | t', (n, None  ) -> cxt               , (n, Some t')::params
             | t', (n, Some t) -> unifytype cxt t t', (n, Some t')::params
           in
           let cxt, params = List.fold_right stitch (zip chants params) (cxt, []) in
           do_procparams "Read" cxt params proc 
       | Write (chan, es) ->
           let chants = List.map (fun _ -> new_TypeVar()) es in 
           let chant = Type.delist chants in
           let cxt = assigntype_expr cxt (Channel chant) chan in
           let cxt = List.fold_left (fun cxt (t,v) -> assigntype_expr cxt t v) cxt (zip chants es) in
           typecheck_process cxt proc
       | Measure (e, param) ->
           let cxt, param = 
             match param with 
             | n, None   -> cxt, (n, Some Bit)
             | n, Some t -> unifytype cxt t Bit, param
           in
           let cxt = assigntype_expr cxt Qbit e in
           do_procparams "Measure" cxt [param] proc
       | Ugatestep (es, ugate) ->
           let cxt = List.fold_left (fun cxt e -> assigntype_expr cxt Qbit e) cxt es in
           let arity, cxt = typecheck_ugate cxt ugate in
           if List.length es <> arity then 
             raise (TypeCheckError ("arity mismatch in " ^ string_of_step step))
           ;
           typecheck_process cxt proc
       | Eval (e) -> (* probably obsolete *)
           let cxt = assigntype_expr cxt Unit e in
           typecheck_process cxt proc
      )
  | Cond (e,p1,p2) ->
      let cxt = assigntype_expr cxt Bool e in
      let cxt = typecheck_process cxt p1 in
      typecheck_process cxt p2
  | Par (ps) -> List.fold_left typecheck_process cxt ps

let typecheck_processdef cxt (Processdef (n,params,proc)) =
  let cxt = do_procparams "processdef" cxt params proc in
  let cxt = evalcxt cxt in
  (* Printf.printf "after %s cxt = %s\n" (string_of_name n) (string_of_typecxt cxt); *)
  cxt
  
let typecheckdefs lib defs =
  (* lib is a list of name:type pairs, and most of the types have typevars. Convert to Univ types. *)
  let generalise (n,t) = 
    let vs = Type.frees t in
    n, if NameSet.is_empty vs then t else Univ(NameSet.elements vs,t)
  in
  List.iter (fun (n,t) -> match t with Process _ -> ok_procname n | _ -> ()) lib;
  let cxt = List.map generalise lib in
  let header_type cxt (Processdef (n,ps,_) as def) =
    ok_procname n;
    let process_param = function
    | _, None   -> TypeVar (new_unknown_name())
    | n, Some t -> if (match t with Univ _ -> true | _ -> false) ||
                      not (NameSet.is_empty (Type.frees t)) 
                   then raise (TypeCheckError (Printf.sprintf "Error in %s: process parameter cannot be given a universal type"
                                                              (string_of_param (n,Some t))
                                              )
                              )
                   ;
                   (match t with Process _ -> ok_procname n | _ -> ())
                   ;
                   t
    in
    let process_params = List.map process_param in
    if cxt<@?>n 
    then raise (TypeCheckError (Printf.sprintf "Error in %s: previous definition of %s" 
                                               (string_of_processdef def)
                                               (string_of_name n)
                               )
               )
    else (n, Process (process_params ps))::cxt
  in
  let cxt = List.fold_left header_type cxt defs in
  let cxt = List.fold_left typecheck_processdef cxt defs in
  if !verbose || !verbose_typecheck then print_endline ("typechecked");
