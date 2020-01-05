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
open Instance
open Sourcepos
open Listutils
open Tupleutils
open Functionutils
open Optionutils
open Expr
open Basisv
open Process
open Def
open Step
open Pattern

exception Error of sourcepos * string

(* Sestoft's pattern-match compiler, from ML pattern match compilation and partial evaluation. *)

(* It's clear where incompleteness comes out: see Failure. It's not yet clear to me where redundancy 
   comes out. Hmmm.
 *)

type constructor =
  | CCons   
  | CNil
  | CTuple  
  | CInt    of int
  | CBool   of bool
  | CChar   of char
  | CString of string
  | CBit    of bool          
  | CUnit          
  | CBasisv of basisv
  | CGate   of string    

type con = {con:constructor; arity:int; span:int}

type termd = Pos of con * termd list | Neg of con list

type cxt = (con * termd list) list

type path = Obj | Sel of int * path

type 'a dtree = Failure | Success of 'a | IfEq of path * con * 'a dtree * 'a dtree

type answer = Yes | No | Maybe

let string_of_constructor = function
  | CCons       -> "CCons"
  | CNil        -> "CNil"
  | CTuple      -> "CTuple"
  | CInt    i   -> Printf.sprintf "CInt %d" i 
  | CBool   b   -> Printf.sprintf "CBool %B" b
  | CChar   c   -> Printf.sprintf "CChar'%s'" (Char.escaped c)
  | CString s   -> Printf.sprintf "CString\"%s\"" (String.escaped s)
  | CBit    b   -> Printf.sprintf "CBit 0b%d" (if b then 1 else 0)           
  | CUnit       -> "CUnit"          
  | CBasisv bv  -> Printf.sprintf "CBasisv %s" (string_of_basisv bv)
  | CGate   s   -> Printf.sprintf "CGate %s" s   

let short_string_of_constructor = function
  | CCons           -> "::"
  | CNil            -> "Nil"
  | CTuple          -> "CTuple"
  | CInt    i       -> Printf.sprintf "%d" i 
  | CBool   b       -> Printf.sprintf "%B" b
  | CChar   c       -> Printf.sprintf "'%s'" (Char.escaped c)
  | CString s       -> Printf.sprintf "\"%s\"" (String.escaped s)
  | CBit    b       -> Printf.sprintf "0b%d" (if b then 1 else 0)           
  | CUnit           -> "CUnit"          
  | CBasisv bv      -> Printf.sprintf "%s" (string_of_basisv bv)
  | CGate   "Phi"   -> "Phi _"
  | CGate   s       -> s

let string_of_con con =
  Printf.sprintf "{con=%s;arity=%d;span=%d}" 
                 (string_of_constructor con.con)
                 con.arity
                 con.span

let short_string_of_con c = short_string_of_constructor c.con

let rec string_of_termd = function
  | Pos (con,termds) -> Printf.sprintf "Pos(%s,%s)" (string_of_con con) (bracketed_string_of_list string_of_termd termds)
  | Neg cons         -> Printf.sprintf "Neg%s" (bracketed_string_of_list string_of_con cons)
  
let rec string_of_path = function
  | Obj       -> "Obj"
  | Sel (i,a) -> Printf.sprintf "%s.%d" (string_of_path a) i
  
let rec string_of_dtree string_of_rhs = function
  | Failure     -> "Failure"
  | Success s   -> Printf.sprintf "Success (%s)" (string_of_rhs s) 
  | IfEq (a,c,dt1,dt2) -> Printf.sprintf "IfEq %s.0 %s (%s) (%s)" 
                                         (string_of_path a)
                                         (short_string_of_con c)
                                         (string_of_dtree string_of_rhs dt1)
                                         (string_of_dtree string_of_rhs dt2)

let string_of_answer = function 
  | Yes     -> "Yes" 
  | No      -> "No" 
  | Maybe   -> "Maybe"
  

let string_of_cxt = bracketed_string_of_list (string_of_pair string_of_con (bracketed_string_of_list string_of_termd) ",")

let string_of_workel =
  string_of_triple (bracketed_string_of_list string_of_pattern)
                   (bracketed_string_of_list string_of_path)
                   (bracketed_string_of_list string_of_termd)
                   ","

let string_of_work = bracketed_string_of_list string_of_workel

let rec builddsc cxt dsc work =
  let r = match cxt, work with
          | []             , []                -> dsc
          | (con,args)::cxt, (_,_,dargs)::work -> builddsc cxt (Pos (con, List.rev args @ (dsc::dargs))) work
          | _                                  -> raise (Can'tHappen (Printf.sprintf "builddsc %s %s %s"
                                                                                     (string_of_cxt cxt)
                                                                                     (string_of_termd dsc)
                                                                                     (string_of_work work)
                                                                     )
                                                        )
  in
  if !verbose then
    Printf.printf "builddsc %s %s %s => %s\n"
                  (string_of_cxt cxt)
                  (string_of_termd dsc)
                  (string_of_work work)
                  (string_of_termd r);
  r

let augment cxt termd =
  let r = match cxt with
          | []              -> []
          | (con,args)::cxt -> (con,termd::args)::cxt
  in
  if !verbose then
    Printf.printf "augment %s %s => %s\n"
                  (string_of_cxt cxt)
                  (string_of_termd termd)
                  (string_of_cxt r);
  r

let norm cxt = 
  let r = match cxt with 
          | []               -> []
          | (con,args)::cxt -> augment cxt (Pos (con, List.rev args))
  in
  if !verbose then
    Printf.printf "norm %s => %s\n"
                  (string_of_cxt cxt)
                  (string_of_cxt r);
  r

let addneg termd con = 
  match termd with
  | Neg nonset -> let r = Neg (con::nonset) in
                  if !verbose then
                    Printf.printf "addneg %s %s => %s\n"
                                  (string_of_termd termd)
                                  (string_of_con con)
                                  (string_of_termd r);
                  r
  | _          -> raise (Can'tHappen (Printf.sprintf "addneg %s %s" 
                                                     (string_of_termd termd) 
                                                     (string_of_con con)
                                     )
                        )

let staticmatch con termd =
  let r = match termd with
          | Neg ns -> if List.exists (fun ncon -> ncon=con) ns then No
                      else
                      if List.length ns = con.span-1 then Yes
                      else Maybe
          | Pos(pcon,_) -> if pcon=con then Yes else No
  in
  if !verbose then 
    Printf.printf "staticmatch %s (%s) => %s\n"
                  (string_of_con con)
                  (string_of_termd termd)
                  (string_of_answer r);
  r

(* rhs and pattern things have to be instances. Luckily expr and process each is an instance *)

let matchcheck_pats string_of_rhs rules = 

  let string_of_rules rules = "[" ^  string_of_list (string_of_pair string_of_pattern string_of_rhs ".") " <+> " rules ^ "]" in
  
  let sps = List.map (fun rule -> (fst rule).pos) rules in
  let patspos = sp_of_sps sps in
  
  let successes = Hashtbl.create (List.length rules) in         (* a sourcepos-indexed record of successes in the tree *)
  
  let show_fail dsc =
    let neginfo neg negs =
      let several words =
        Printf.sprintf "%s which is %s %s" 
                       words 
                       (match negs with [] -> "not" | _ -> "neither")
                       (String.concat " nor " (List.sort Stdlib.compare (List.map short_string_of_con (neg::negs))))
      in
      match neg.con with
      | CCons       -> "an empty list"
      | CNil        -> "a non-empty list"
      | CUnit            
      | CTuple      -> raise (Can'tHappen (Printf.sprintf "show_fail (%s) -- first Neg element?" 
                                                          (string_of_termd dsc)
                                          )
                             )
      | CInt    i   -> several "an integer" 
      | CBool   b   -> Printf.sprintf "%B" (not b)
      | CChar   c   -> several "a char"
      | CString s   -> several "a string"
      | CBit    b   -> Printf.sprintf "0b%d" (if not b then 1 else 0)           
      | CBasisv bv  -> several "a basis vector" 
      | CGate   s   -> several "a gate" 
                      
    in
    let rec posinfo x con args =
      let rec phrase = function
        | []            -> raise (Can'tHappen ("phrase []"))
        | [ws]          -> ws
        | [ws1;ws2]     -> ws1 ^ " and " ^ ws2
        | ws::wheres    -> ws ^ ", " ^ phrase wheres
      in
      let witharg (name,arg) =
        match arg with
        | Neg []          -> ""
        | Neg (neg::negs) -> Printf.sprintf "%s is %s" name (neginfo neg negs)
        | Pos (con,args)  -> Printf.sprintf "%s is %s" name (posinfo (x^"x") con args)
      in
      let withargs words arginfos =
        let arginfos = List.map (fun (_,x,arg) -> x,arg) (List.filter fstof3 arginfos) in
        let wheres = List.map witharg arginfos in
        let wheres = List.filter (fun s -> s<>"") wheres in
        Printf.sprintf "%s, where %s" words (phrase wheres)
      in
      let constinfo arg =
        match arg with 
        | Pos (con, args) ->
            (match con.con with
             | CCons   
             | CTuple  
             | CGate   "Phi" -> None    
             | _             -> Some (short_string_of_con con)
            )
        | Neg []          -> Some "_"
        | _               -> None
      in
      let arginfo namedargs =
        let arginfo (i,(name,arg)) =
          match constinfo arg with
          | Some info -> false, info             , arg
          | None      -> true , x^string_of_int i, arg
        in
        List.map arginfo (numbered namedargs)
      in
      match con.con, args with
      | CCons      , [_;_] -> let names = [x;x^"s"] in
                              let arginfos = arginfo (zip names args) in
                              let words = Printf.sprintf "a list %s::%ss" 
                                                         (sndof3 (List.hd arginfos)) 
                                                         (sndof3 (List.hd (List.tl arginfos))) 
                              in
                              withargs words arginfos
      | CTuple     , _     -> let names = tabulate (List.length args) (fun i -> x^string_of_int i) in
                              let arginfos = arginfo (zip names args) in
                              withargs (Printf.sprintf "a tuple (%s)" (string_of_list sndof3  "," arginfos)) arginfos
      | CGate "Phi", [a]   -> let arginfos = arginfo [x,a] in
                              withargs (Printf.sprintf "Phi(%s)" (sndof3 (List.hd arginfos))) arginfos      
      | _                  -> short_string_of_con con
    in
    match dsc with
    | Neg (neg::negs)  -> 
        Printf.eprintf "Warning! %s: this match is incomplete. It will fail on %s\n"
                      (string_of_sourcepos patspos)
                      (neginfo neg negs)
    | Neg []         -> 
        Printf.eprintf "Warning! %s: this match has no patterns. It is certain to fail\n" (string_of_sourcepos patspos)
    | Pos (con,args) -> 
        Printf.eprintf "Warning! %s: this match is incomplete. It will fail on %s\n" 
                                      (string_of_sourcepos patspos)
                                      (posinfo "x" con args)
  in
  
  let rec fail dsc rules =
    if !verbose then
      Printf.printf "fail %s %s\n"
                    (string_of_termd dsc) 
                    (string_of_rules rules);
    match rules with
    | []               -> show_fail dsc;
                          Failure
    | (pat,rhs)::rules -> _match pat Obj dsc [] [] rhs rules
  
  and succeed cxt work rhs rules =
    if !verbose then
      Printf.printf "succeed %s %s %s %s\n"
                    (string_of_cxt cxt) 
                    (string_of_work work) 
                    (string_of_rhs rhs) 
                    (string_of_rules rules);
    match work with
    | []      -> Hashtbl.add successes rhs.pos true;
                 Success rhs 
    | w::work -> (match w with
                    [],[],[]                        -> succeed (norm cxt) work rhs rules 
                  | pat::pats, obj::objs, dsc::dscs -> _match pat obj dsc cxt ((pats,objs,dscs)::work) rhs rules
                  | pats,objs,dscs                  -> raise (Can'tHappen (Printf.sprintf "succeed w = %s"
                                                                                          (string_of_workel w)
                                                                          )
                                                             )
                 )
  
  and _match pat obj dsc cxt work rhs rules =
    if !verbose then
      Printf.printf "_match (%s) %s %s %s %s (%s) %s\n"
                    (string_of_pattern pat) 
                    (string_of_path obj) 
                    (string_of_termd dsc) 
                    (string_of_cxt cxt) 
                    (string_of_work work) 
                    (string_of_rhs rhs) 
                    (string_of_rules rules);
    let casopt = match pat.inst.pnode with
                 | PatAny
                 | PatName   _      -> None
                 | PatUnit          -> Some ({con=CUnit     ; arity=0             ; span=1       }, []   ) 
                 | PatNil           -> Some ({con=CNil      ; arity=0             ; span=2       }, []   )
                 | PatInt    i      -> Some ({con=CInt    i ; arity=0             ; span= -1     }, []   )
                 | PatBit    b      -> Some ({con=CBit    b ; arity=0             ; span=2       }, []   )
                 | PatBool   b      -> Some ({con=CBool   b ; arity=0             ; span=2       }, []   )
                 | PatChar   c      -> Some ({con=CChar   c ; arity=0             ; span=128     }, []   )
                 | PatString s      -> Some ({con=CString s ; arity=0             ; span=(-1)    }, []   )
                 | PatBasisv bv     -> Some ({con=CBasisv bv; arity=0             ; span=nBasisv }, []   )
                 | PatCons   (h,t)  -> Some ({con=CCons     ; arity=2             ; span=2       }, [h;t])
                 | PatTuple  ps     -> Some ({con=CTuple    ; arity=List.length ps; span=1       }, ps   )
    in
    match casopt with
    | None             -> 
        succeed (augment cxt dsc) work rhs rules
    | Some (con,cargs)  -> 
        let args f = tabulate con.arity f in
        let getdargs termd =
          match termd with
          | Neg _            -> args (fun _ -> Neg [])
          | Pos (con,termds) -> termds
        in
        let getoargs () = args (fun i -> Sel (i+1,obj)) in
        let succeed' () =
          succeed ((con,[])::cxt) ((cargs,getoargs(),getdargs dsc)::work) rhs rules
        in
        let fail' dsc = fail (builddsc cxt dsc work) rules in
        match staticmatch con dsc with
        | Yes    -> succeed' ()
        | No     -> fail' dsc         (* this is redundancy, I think *) 
        | Maybe  -> IfEq (obj, con, succeed' (), fail' (addneg dsc con))
  in 
  if !verbose then
    Printf.printf "\nmatchcheck_pats %s\n" (string_of_rules rules);
  let dtree = fail (Neg []) rules in
  if !verbose then 
    Printf.printf "\nmatchcheck_pats %s %s => %s\n\n" 
                  (string_of_sourcepos patspos)
                  (string_of_rules rules)
                  (string_of_dtree string_of_rhs dtree);
  let redundancy (pat,rhs) = if Hashtbl.mem successes rhs.pos then ()
                             else Printf.eprintf "Warning! %s: this pattern is redundant (can never match)\n"
                                  (string_of_sourcepos pat.pos)
  in
  List.iter redundancy rules

let rec matchcheck_expr e =
  if !verbose then 
    Printf.printf "\nmatchcheck_expr %s\n" (string_of_expr e);
  match e.inst.tinst with
  | EUnit
  | EVar        _
  | ENum        _
  | EBool       _
  | EChar       _
  | EString     _
  | EBit        _
  | EBasisv     _
  | ENil                    -> ()
  | EMinus      e           
  | ENot        e           -> matchcheck_expr e
  | ETuple      es          -> List.iter matchcheck_expr es
  | ECond       (ce,e1,e2)  -> matchcheck_expr ce; matchcheck_expr e1; matchcheck_expr e2
  | EMatch      (e,ems)     -> matchcheck_expr e; 
                               matchcheck_pats string_of_expr ems;
                               List.iter (matchcheck_expr <.> snd) ems
  | EArith      (e1,_,e2)
  | ECompare    (e1,_,e2)
  | EBoolArith  (e1,_,e2)   -> matchcheck_expr e1; matchcheck_expr e2
  | ECons       (e1,e2)
  | EApp        (e1,e2)
  | EAppend     (e1,e2)     -> matchcheck_expr e1; matchcheck_expr e2
  | ELambda     (pats,e)    -> matchcheck_expr e
  | EWhere      (e,ed)      -> matchcheck_expr e; matchcheck_edecl ed
  
and matchcheck_edecl edecl = 
  match edecl.inst with
  | EDPat (wpat,_,we)        -> matchcheck_expr we
  | EDFun (wfn,wfpats,_, we) -> matchcheck_expr we

let rec matchcheck_proc mon proc =
  if !verbose then 
    Printf.printf "\nmatchcheck_proc %s\n" (short_string_of_process proc);
  match proc.inst with
  | Terminate               -> ()
  | GoOnAs          (pn,es)   -> List.iter matchcheck_expr es
  | WithNew   (params,proc) -> matchcheck_proc mon proc    
  | WithQbit  (qspecs,proc) -> let matchcheck_qspec = function
                                 | param, Some e -> matchcheck_expr e
                                 | param, None   -> ()
                               in
                               List.iter matchcheck_qspec qspecs;
                               matchcheck_proc mon proc
  | WithLet   ((_,e), proc) -> matchcheck_expr e; matchcheck_proc mon proc (* binding pattern doesn't need check *)
  | WithProc  ((_,_,_,p),proc) -> matchcheck_proc mon p; matchcheck_proc mon proc
  | WithQstep (qstep,proc)  -> (match qstep.inst with
                                | Measure   (qe, gopt, _)   -> matchcheck_expr qe; (matchcheck_expr ||~~ ()) gopt
                                | Ugatestep (qes,ge)           -> List.iter matchcheck_expr qes; matchcheck_expr ge
                               ); 
                               matchcheck_proc mon proc 
  | TestPoint (n, proc)     -> (match find_monel n.inst mon with
                                | Some (_,monproc) -> matchcheck_proc mon monproc
                                | None             -> raise (Can'tHappen (Printf.sprintf "%s: matchcheck_proc sees no monproc"
                                                                                           (string_of_sourcepos n.pos)
                                                                         )
                                                            )
                               );
                               matchcheck_proc mon proc
  | Iter      (params, p, e, proc)
                            -> matchcheck_proc mon p; matchcheck_expr e; matchcheck_proc mon proc
  | Cond      (e,p1,p2)     -> matchcheck_expr e; matchcheck_proc mon p1; matchcheck_proc mon p2 
  | PMatch    (e,pms)       -> matchcheck_expr e; 
                               matchcheck_pats short_string_of_process pms;
                               List.iter (matchcheck_proc mon <.> snd) pms
  | GSum      iops          -> let matchcheck_iop (iostep, proc) =
                                 (match iostep.inst with
                                  | Read  (ce,_) -> matchcheck_expr ce   (* binding pattern doesn't need check *)
                                  | Write (ce,e) -> matchcheck_expr ce; matchcheck_expr e
                                 );
                                 matchcheck_proc mon proc
                               in
                               List.iter matchcheck_iop iops
  | Par       ps            -> List.iter (matchcheck_proc mon) ps

let matchcheck_def def =
  if !verbose then 
    Printf.printf "\nmatchcheck_def %s\n" (string_of_def def);
  match def with
  | Processdefs  pdefs                 -> let pcheck (pn, _, proc, mon) = matchcheck_proc mon proc in
                                          List.iter pcheck pdefs
  | Functiondefs fdefs                 -> let fcheck (fn, pats, _, expr) = matchcheck_expr expr in
                                          List.iter fcheck fdefs
  | Letdef       (pat, e)              -> matchcheck_expr e
  
let matchcheck defs = push_verbose !verbose_matchcheck (fun () -> List.iter matchcheck_def defs)
