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
open Braket
open Pattern
open Type
open Param
open Cbasics
open Cstep
open Cprocess
open Def
open Qsim
open Number
open Monenv
open Compile

open Vt
open Value
open Snum
open Vmg

open Event

exception Error of sourcepos * string
exception MatchError of sourcepos * string
exception Disaster of sourcepos * string

let (<@>)  env n     = try Monenv.(<@>) env n 
                       with Not_found -> raise (Disaster (dummy_spos, 
                                                          Printf.sprintf "looking up %s in %s"
                                                                         (string_of_name n)
                                                                         (short_string_of_env env)
                                                         )
                                               )       

(* I think I can do without this comfort blanket
   let miseval s v = raise (Error (dummy_spos, Printf.sprintf "%s (%s)" s (string_of_value v)))

   let unitv   = function VUnit           -> ()     | v -> miseval "unitv"    v
   let bitv    = function VBit    b       -> b      | v -> miseval "bitv"     v
   let numv    = function VNum    n       -> n      | v -> miseval "numv"     v
   let boolv   = function VBool   b       -> b      | v -> miseval "boolv"    v
   let charv   = function VChar   c       -> c      | v -> miseval "charv"    v
   let sxnumv  = function VSxnum  n       -> n      | v -> miseval "sxnumv"   v
   (* let stringv = function VString s       -> s      | v -> miseval "stringv"  v *)
   let stringv = function VList   vs      -> let cs = List.map charv vs in
                                             Utf8.string_of_uchars cs
                                                    | v -> miseval "stringv"  v
   let brav    = function VBra    b       -> b      | v -> miseval "brav"     v
   let ketv    = function VKet    k       -> k      | v -> miseval "ketv"     v
   let matrixv = function VMatrix m       -> m      | v -> miseval "matrixv"  v
   let gatev   = function VGate   g       -> g      | v -> miseval "gatev"    v
   let chanv   = function VChan   c       -> c      | v -> miseval "chanv"    v
   let qbitv   = function VQbit   q       -> q      | v -> miseval "qbitv"    v
   let qbitsv  = function VQbits  qs      -> qs     | v -> miseval "qbitsv"    v
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
   let vsxnum  n       = VSxnum  n
   (* let vstring s       = VString s *)
   let vstring s       = VList (List.map vchar (Utf8.uchars_of_string s))
   let vbra    b       = VBra    b
   let vket    k       = VKet    k
   let vmatrix m       = VMatrix m
   let vgate   g       = VGate   g
   let vchan   c       = VChan   c
   let vqbit   q       = VQbit   q
   let vqbits  qs      = VQbits  qs
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
 *)     
 
(* bring out your dead: a nasty space leak plugged *)
let rec boyd pq = 
  try let _, gsir = Ipq.first pq in
      let b, _ = !gsir in
      if b then () else (Ipq.remove pq; boyd pq)
  with Ipq.Empty -> ()

;; (* to give boyd a polytype *)

(* predefined channels *)
let dispose_c = -1
let out_c     = -2
let outq_c    = -3
let in_c      = -4

(* ******************** the interpreter proper ************************* *)

let mkchan c traced = {cname=c; traced= traced;
                                stream=Queue.create (); 
                                rwaiters=Ipq.create 10; (* 10 is a guess *)
                                wwaiters=Ipq.create 10; (* 10 is a guess *)
                      }

module OrderedChan = struct type t = chan 
                            let compare c1 c2 = Stdlib.compare c1.cname c2.cname
                            let to_string c = string_of_int c.cname
                     end
module ChanSet = MySet.Make (OrderedChan)

type gsum = Grw of rwaiter | Gww of wwaiter

let pq_push pq = Ipq.push pq (Random.bits ())

let pq_excite pq = Ipq.excite (fun i -> i/2) pq

let stepcount = ref 0

let evale env e = e env

let rec interp env proc =
  Qsim.init ();
  let chancount = ref 0 in
  let stuck_chans = ref ChanSet.empty in (* no more space leak: this is for stuck channels *)
  let string_of_stuck_chans () = ChanSet.to_string !stuck_chans in
  let remember_chan c = stuck_chans := ChanSet.add c !stuck_chans in
  let maybe_forget_chan c =
    boyd c.rwaiters;
    boyd c.wwaiters;
    if Queue.is_empty c.stream && 
       Ipq.is_empty c.rwaiters &&
       Ipq.is_empty c.wwaiters
    then
      stuck_chans := ChanSet.remove c !stuck_chans
  in
  let newchan b = 
    let c = !chancount in 
    chancount := !chancount+1; 
    let chan = mkchan c b in
    of_chan chan 
  in
  let (procnames: (name,unit) Hashtbl.t) = Hashtbl.create 100 in    
  let runners = Ipq.create (10) in (* 10 is a guess *)
  let addrunner runner = pq_push runners runner in
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
      if Ipq.is_empty runners then 
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
              (print_interp_state stdout; flush_all ());
            let runner = Ipq.pop runners in
            pq_excite runners;
            let pn, rproc, env = runner in
            let show_pstep s =
                 Printf.printf "%s %s: %s %s" (string_of_sourcepos (csteppos rproc)) pn s (string_of_env env);
                 let _ = read_line () in
                 ()
            in
            let pstep_state env =
              let env_string = if not (Monenv.null env) then 
                                 Printf.sprintf "  %s\n" (string_of_env env)
                               else ""
              in
              Printf.sprintf "%s  %s" env_string (string_of_qstate())
            in
            let pstep_env env' env =
              let assoc = assoc_of_monenv env in
              let assoc' = assoc_of_monenv env' in
              let assoc'' = take (List.length assoc' - List.length assoc)  assoc' in
              if assoc''<>[] then Printf.sprintf "\n  binds %s" (string_of_monassoc "=" string_of_vt assoc'')
              else ""
            in
              ((try
                  match rproc.inst with
                  | CTerminate           -> deleteproc pn; if !pstep then show_pstep "_0"
                  | CGoOnAs (gpn, es) -> 
                      (let vs = List.map (evale env) es in
                       let pv = 
                         try env<@>tinst gpn 
                         with Not_found -> raise (Error (rproc.pos, Printf.sprintf "** Disaster: no process called %s" 
                                                                                        (string_of_name (tinst gpn))
                                                        )
                                                 )
                      in
                      let (n, er, ns, proc) = to_procv pv in
                      let locals = zip ns vs in
                      let env = monenv_of_lg locals !er in
                      deleteproc pn;
                      let gpn' = addnewproc n in
                      addrunner (gpn', proc, env);
                      if !traceId then trace (EVChangeId (pn, [gpn']));
                      if !pstep then
                        show_pstep (Printf.sprintf "%s(%s)" 
                                                   (tinst gpn) 
                                                   (string_of_list string_of_vt "," vs)
                                   )
                      )
                  | CWithNew ((traced, ps), proc) ->
                      let ps' = List.map (fun p -> (name_of_param p, newchan traced)) ps in
                      let env' = List.fold_left (<@+>) env ps' in
                      addrunner (pn, proc, env');
                      if !pstep then 
                        show_pstep (Printf.sprintf "(new %s)" (commasep (List.map string_of_param ps)))
                  | CWithQbit (plural, qss, proc) -> 
                      let ket_eval vopt = vopt &~~ fun ke -> Some (to_ket (ke env)) in
                      let qss' = List.map (fun (par,vopt) -> let n = name_of_param par in 
                                                             let kopt = ket_eval vopt in
                                                             (par.pos, n, kopt, newqbits pn n kopt)
                                          ) 
                                          qss 
                      in
                      let do_q env (pos, n, kopt, qs) =
                        match plural, qs with
                        | true , qs  -> env <@+> (n, of_qbits qs)
                        | false, [q] -> env <@+> (n, of_qbit q)
                        | false, qs  -> raise (Can'tHappen (Printf.sprintf "single qbit %s initialised to %s"
                                                                                       (string_of_name n)
                                                                                       (string_of_ket (_The kopt))
                                                     )
                                              )
                      in
                      let env' = List.fold_left do_q env qss' in
                      addrunner (pn, proc, env');
                      if !pstep then 
                        show_pstep (Printf.sprintf "(newq %s)\n%s" (commasep (List.map string_of_cqspec qss)) (pstep_state env'))
                  | CWithLet ((pat,e), proc) ->
                      let v = e env in
                      addrunner (pn, proc, pat env v);
                      if !pstep then 
                        show_pstep (Printf.sprintf "(let %s)" (string_of_cletspec (pat,e)))
                  | CWithProc ((brec,pn',params,proc),p) ->
                      let er = ref env in
                      let procv = (tinst pn', er, names_of_params params, proc) in
                      let env = env<@+>(tinst pn', of_procv procv) in
                      if brec then er := env;
                      addrunner (pn, p, env)
                  | CWithQstep (qstep, proc) ->
                      (let qeval plural e = (if plural then to_qbits else (fun v -> [to_qbit v])) (evale env e) in
                       match qstep.inst with
                       | CMeasure (plural, e, gopt, pat) -> 
                           let qs = qeval plural e in
                           (* measurement without detection is absurd, wrong. So we ignore pat when disposing *)
                           let disposed = !measuredestroys in
                           let aqs = 
                             if !traceevents then 
                               let allqs = fst (qval_of_qs qs) in
                               List.fold_left (fun qs q -> if disposed then Listutils.remove q qs else qs)
                                              allqs
                                              qs
                             else 
                               qs
                           in
                           let gv = ((to_gate <.> evale env) ||~~ g_I) gopt in
                           let bs = List.map (fun q -> qmeasure disposed pn gv q = 1) qs in
                           if !traceevents then trace (EVMeasure (pn, qs, gv, bs, tev aqs));
                           let vs = List.map of_bit bs in
                           let env' = pat env (if plural then of_list vs else List.hd vs) in
                           addrunner (pn, proc, env');
                           if !pstep then 
                             show_pstep (Printf.sprintf "%s\n%s%s" (string_of_cqstep qstep) 
                                                                   (pstep_state env')
                                                                   (pstep_env env' env)
                                        )
                       | CThrough (plural, es, g)      -> 
                           let qs = List.concat (List.map (qeval plural) es) in
                           let g = to_gate (evale env g) in
                           let qvs = if !traceevents then tev qs else [] in
                           ugstep pn qs g;
                           addrunner (pn, proc, env);
                           if !traceevents then trace (EVGate (pn, qvs, g, tev qs));
                           if !pstep then 
                             show_pstep (Printf.sprintf "%s\n%s" (string_of_cqstep qstep) (pstep_state env))
                      )
                  | CJoinQs (qns, qp, proc) ->
                      let do_qn qn =
                        to_qbits (try env<@>tinst qn
                                  with Not_found -> 
                                    raise (Error (qn.pos, "** Disaster: unbound " ^ string_of_name (tinst qn)))
                                 )
                      in
                      let qs = List.concat (List.map do_qn qns) in
                      let env = env<@+>(name_of_param qp, of_qbits qs) in
                      addrunner (pn, proc, env);
                      if !pstep then
                        show_pstep (Printf.sprintf "(joinqs %s→%s)\n%s" (string_of_list string_of_typedname "," qns) (string_of_param qp) (pstep_state env))
                  | CSplitQs (qn, qspecs, proc) -> 
                      let qvs = to_qbits (try env<@>tinst qn
                                          with Not_found -> 
                                            raise (Error (qn.pos, "** Disaster: unbound " ^ string_of_name (tinst qn)))
                                         )
                      in
                      let do_spec qns (qp, eopt) =
                        let numopt = eopt &~~ (_Some <.> to_num <.> evale env) in
                        let n = match numopt with 
                                | None   -> 0 
                                | Some n -> if n<=/num_0 || not (is_int n) then
                                               raise (Error (rproc.pos, Printf.sprintf "%s is invalid qbits size" (string_of_num n)))
                                            else int_of_num n
                        in
                        (qp,n)::qns
                      in
                      let qpns = List.fold_left do_spec [] qspecs in
                      let avail = List.length qvs in
                      let total = List.fold_left (fun total (_,n) -> total+n) 0 qpns in
                      let zeroes = List.length (List.filter (fun (_,n) -> n=0) qpns) in
                      if zeroes > 1 then 
                        raise (Error (rproc.pos, "** Disaster: more than one un-sized qbits sub-collection"))
                      else
                      if zeroes = 0 && total<>avail then
                         raise (Error (rproc.pos, Printf.sprintf "%d qbits split into total of %d" avail total))
                      else
                      if total>=avail then 
                         raise (Error (rproc.pos, Printf.sprintf "%d qbits split into total of %d and then one more" avail total))
                      ;
                      let spare = avail-total in
                      let carve (env,qvs) (qp,n) =
                        let k = if n=0 then spare else n in
                        if k>List.length qvs then 
                          raise (Disaster (rproc.pos, "taken too many in carve"));
                        let qvs1, qvs = take k qvs, drop k qvs in
                        env<@+>(name_of_param qp, of_qbits qvs1), qvs
                      in
                      let env,qvs = List.fold_left carve (env,qvs) qpns in
                      if qvs<>[] then raise (Disaster (rproc.pos, "not taken enough in carve"));
                      addrunner (pn, proc, env);
                      if !pstep then
                        show_pstep (Printf.sprintf "(splitqs %s→%s)\n%s" 
                                                     (string_of_typedname qn) 
                                                     (string_of_list string_of_csplitspec "," qspecs) 
                                                     (pstep_state env)
                                   )
                  | CGSum ioprocs      -> 
                      let withdraw chans = List.iter maybe_forget_chan chans in (* kill the space leak! *)
                      let canread pos c tpat pat =
                        let can'tread s = raise (Error (pos, "cannot read from " ^ s ^ " channel (this should be a type error -- sorry)")) in
                        let do_match v = Some (pat env v) in
                        try if c.cname = dispose_c then can'tread "dispose" 
                            else
                            if c.cname = out_c || c.cname = outq_c then can'tread "output"
                            else
                            if c.cname = in_c then 
                              (let v = hide_string (read_line ()) in
                               if !traceIO then trace (EVInput (pn, (tpat,v)));
                               do_match v
                              )
                            else
                              let v' = Queue.pop c.stream in
                              (maybe_forget_chan c; do_match v')
                        with Queue.Empty ->
                        try boyd c.wwaiters; (* now the first must be alive *)
                            let (pn',v',proc',env'),gsir = Ipq.pop c.wwaiters in
                            let _, chans = !gsir in
                            gsir := false, [];
                            withdraw chans;
                            pq_excite c.wwaiters;
                            addrunner (pn', proc', env');
                            if !traceevents && c.traced then trace (EVMessage (c, pn', pn, (tpat,v')));
                            do_match v'
                        with Ipq.Empty -> None
                      in
                      let canwrite pos c t v =
                        let can'twrite s = raise (Error (pos, "cannot write to " ^ s ^ " channel (this should be a type error -- sorry)")) in
                        if c.cname = in_c then can'twrite "input"
                        else
                        if c.cname = dispose_c then 
                           (disposeqbits pn [to_qbit v]; 
                            if !traceevents then trace (EVDispose (pn,(t,v)));
                            true
                           )
                        else
                        if c.cname = out_c then
                          (let s = String.concat "" (List.map reveal_string (to_list v)) in
                           print_string s; flush stdout; 
                           if !traceIO then trace (EVOutput (pn, (t, hide_string s)));
                           true
                          )
                        else
                        if c.cname = outq_c then
                          (let s = reveal_string v in
                           print_string s; flush stdout; 
                           if !traceIO then trace (EVOutput (pn, (t,v)));
                           true
                          )
                        else
                        try boyd c.rwaiters;
                            let (pn',pat',proc',env'),gsir = Ipq.pop c.rwaiters in
                            let _, chans = !gsir in
                            gsir := false, [];
                            withdraw chans;
                            pq_excite c.rwaiters;
                            let env'' = pat' env' v in
                            addrunner (pn', proc', env'');
                            if !traceevents && c.traced then trace (EVMessage (c, pn, pn', (t,v)));
                            true
                        with Ipq.Empty -> 
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
                        try let (iostep,proc) = Ipq.pop pq in
                            match iostep.inst with
                            | CRead (ce,tpat,pat) -> let c = to_chan (evale env ce) in
                                               (match canread iostep.pos c tpat pat with
                                                | Some env' -> addrunner (pn, proc, env');
                                                               if !pstep then 
                                                                 show_pstep (Printf.sprintf "%s%s\n" (string_of_ciostep iostep) 
                                                                                                     (pstep_env env env')
                                                                            )
                                                | None      -> try_iosteps ((c, Grw (pn, pat, proc, env))::gsum) pq
                                               )
                            | CWrite (ce,te,e)  -> let c = to_chan (evale env ce) in
                                               let v = evale env e in
                                               if canwrite iostep.pos c te v then 
                                                 (addrunner (pn, proc, env);
                                                  if !pstep then 
                                                    show_pstep (Printf.sprintf "%s\n  sends %s" (string_of_ciostep iostep) 
                                                                                                (string_of_value te v)
                                                               )
                                                 )
                                               else try_iosteps ((c, Gww (pn, v, proc, env))::gsum) pq
                        with Ipq.Empty ->
                        let cs = List.map fst gsum in
                        let gsir = ref (true, cs) in
                        let add_waiter = function
                          | c, Grw rw -> pq_push c.rwaiters (rw,gsir);
                                         remember_chan c
                          | c, Gww ww -> pq_push c.wwaiters (ww,gsir);
                                         remember_chan c
                        in
                        List.iter add_waiter gsum;
                        if !pstep then 
                          show_pstep (Printf.sprintf "%s\n  blocks" (short_string_of_cprocess rproc))
                      in
                      let pq = Ipq.create (List.length ioprocs) in
                      List.iter (pq_push pq) ioprocs;
                      try_iosteps [] pq
                  | CTestPoint (n, p)  -> raise (Error (n.pos, "TestPoint not precompiled"))
                  | CIter _ -> raise (Error (proc.pos, "Iter not precompiled"))
                  | CCond (e, p1, p2)  ->
                      let bv = to_bool (evale env e) in
                      addrunner (pn, (if bv then p1 else p2), env);
                      if !pstep then 
                        show_pstep (Printf.sprintf "%s (%B)" (short_string_of_cprocess rproc) bv)
                  | CPMatch (e,pms)    -> 
                      let v = evale env e in
                      let env', proc' = pms env v in
                      addrunner (pn, proc', env');
                      if !pstep then 
                        show_pstep (Printf.sprintf "%s\nchose %s%s" (short_string_of_cprocess rproc)
                                                                    (short_string_of_cprocess proc')
                                                                    (pstep_env env' env)
                                   )
                  | CPar ps            ->
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
                        show_pstep (short_string_of_cprocess rproc)
               with
                 | CompileError   _ as exn  -> raise exn  
                 | ExecutionError _ as exn  -> raise exn  
                 | MatchError     _ as exn  -> raise exn
                 | exn                      ->
                     Printf.eprintf "interpreter %s sees exception %s\n" (string_of_sourcepos rproc.pos) (Printexc.to_string exn);
                     print_interp_state stderr;
                     raise exn
             )) (* end of match *)
          with 
          | CompileError   _ as exn  -> raise exn  
          | ExecutionError _ as exn  -> raise exn  
          | MatchError     _ as exn  -> raise exn
          | exn                      ->
              Printf.eprintf "interpreter step () sees exception %s\n" (Printexc.to_string exn);
              print_interp_state stderr;
              raise exn
         ); (* end of try *)
         step()
       ) (* end of else *)
  in
  addrunner ("System", proc, env);
  step ()

(* these are the built-in pdefs -- with newlines and spaces for offside parsing *)

let builtins = [
  "Iter (xs,P,iterc) =                          \n" ^
  "  match xs .                                 \n" ^
  "  + []    . iterc!() . _0                    \n" ^
  "  + x::xs . (new untraced callc : ^())       \n" ^
  "            | P(x,callc)                     \n" ^
  "            | callc?_ . Iter(xs,P,iterc)     \n"
  ;
  "Par (xs, P) =                                \n" ^
  "  match xs .                                 \n" ^
  "  + []     . _0                              \n" ^
  "  + x:: xs . | P(x)                          \n" ^
  "             | Par (xs, P)                   \n"
]

let bind_def : env -> def -> env = fun env ->
  function
  | Processdefs pdefs   -> let env = globalise env in
                           let er = ref env in
                           let env = globalise (List.fold_left (bind_pdef er) env pdefs) in
                           er := env;
                           env
  | Functiondefs fdefs  -> let env = globalise env in
                           let er = ref env in
                           let bind_fdef env (n, pats, _, expr) = env <@+> (tinst n, hide_fun_rec (compile_lambda pats expr) er) in
                           let env = globalise (List.fold_left bind_fdef env fdefs) in
                           er := env;
                           env
  | Letdef (pat, e)     -> (* not recursive, evaluate now *)
                           let fe = compile_expr e in
                           let fpat = compile_bmatch pat Functionutils.id  in
                           let v = evale env fe in
                           globalise (fpat env v)

let interpret defs =
  Random.self_init(); (* for all kinds of random things *)
  (* make an assoc list of library stuff *)
  let knownassoc = let f (n,s,v) =
                     (* let t = generalise (Parseutils.parse_typestring s) in *)
                     n, v
                   in
                   List.map f !Library.knowns in
  (* add standard channels *)
  let definitely_add env (name, c) =
    if env <@?> name then raise (LibraryError ("Whoops! Library has re-defined standard channel " ^ name))
    else env <@+> (name, of_chan (mkchan c true))
  in
  let sysenv = globalise (List.fold_left definitely_add knownassoc 
                                            [("dispose", dispose_c); 
                                             ("out"    , out_c); 
                                             ("outq"   , outq_c); 
                                             ("in"     , in_c)
                                            ]
                        ) 
  in
  (* add built-ins *)
  let bipdefs = List.map (snd <.> precompile_builtin) (List.map Parseutils.parse_pdefstring builtins) in
  let er = ref sysenv in
  let sysenv = globalise (List.fold_left (bind_pdef er) sysenv bipdefs) in
  er := sysenv; 
  (* bind definitions in order *)
  let sysenv = globalise (List.fold_left bind_def sysenv defs) in
  if !verbose || !verbose_interpret then
    Printf.printf "sysenv = %s\n\n" (string_of_env sysenv);
  let sysv = try sysenv <@> "System"
             with Not_found -> raise (Error (dummy_spos, "no System process"))
  in 
  match to_procv sysv with
  |(_, er, [], p) -> flush_all(); interp !er p
  |(_, _ , ps, _) -> raise (Error (dummy_spos, "can't interpret System with non-null parameter list"))
