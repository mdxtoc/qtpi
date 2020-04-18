(*
    Copyright (C) 2019 Richard Bornat
     
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
open Array
open Listutils
open Functionutils
open Optionutils
open Tupleutils
open Value (* for ugv and qbit *)
open Vmg
open Snum
open Forutils
open Braket
open Number (* for num *)

exception Error of string

type qval = qbit list * nv (* with n qbits, 2^n probs in the vector; and it's a ket *)

let string_of_qval_full full (qs,v) =
  match full, qs with
  | false, [_] -> string_of_ket v
  | _          -> Printf.sprintf "[%s]%s"
                          (string_of_list string_of_qbit ";" qs)
                          (string_of_ket v)
                
let string_of_qval = string_of_qval_full false

let qstate = Hashtbl.create ?random:(Some true) 100 (* 100? a guess *)

let init () = Hashtbl.reset qstate

let string_of_qstate () = 
  let qqvs = Hashtbl.fold (fun q qv ss -> (q,qv) :: ss) qstate []
  in
  Printf.sprintf "{%s}" (string_of_list (string_of_pair string_of_qbit string_of_qval " -> ") "; " (List.sort Stdlib.compare qqvs))

let qval q =  try Hashtbl.find qstate q
              with Not_found -> raise (Error (Printf.sprintf "** Disaster: qval with q=%s qstate=%s"
                                                             (string_of_qbit q)
                                                             (string_of_qstate ())
                                             )
                                      )

let qval_of_qs qs = (* qs had better be distinct *)
  let qvals = Listutils.mkset (List.map qval qs) in (* find a faster mkset? *)
  let qss, vs = List.split qvals in
  List.concat qss, List.fold_left tensor_qq nv_1 vs

let qvalmulti = qval_of_qs
  
let tensor_n_gs n g = tensorpow_g g n
              
(* (* I thought this might be quicker than folding, but it isn't *)
   let rec tensor_n_gs n g =
     if n=0 then g_1 else
     if n=1 then g else
                 let g' = tensor_n_gs (n/2) (tensor_gg g g) in 
                 if n mod 2 = 1 then tensor_gg g' g else g'
*)

(* (* memoised seems to make very little difference, or make it worse *)
   module OrderedNG = struct type t = int*gate 
                             let compare = Stdlib.compare
                             let to_string = bracketed_string_of_pair string_of_int string_of_gate
                     end
   module NGMap = MyMap.Make (OrderedNG)
   let memorecNG (f:(int*gate->gate)->int*gate->gate) (s:string) :int*gate->gate = 
     NGMap.memorec id (fun memo (n,g) -> if !verbose || !verbose_qcalc then 
                                           Printf.printf "%s %s %s\n" 
                                                         s (string_of_int n) (string_of_gate g);
                                           f memo (n,g)
                      )

   let tensor_n_gs memo (n,g) =
     if n=0 then g_1 else
     if n=1 then g else
     if n=2 then tensor_gg g g else
                 let g' = memo (n/2, tensor_n_gs 2 g) in 
                 if n mod 2 = 1 then tensor_gg g' g else g'

   let mtn = memorecNG tensor_n_gs "tensor_n_gs"

   let tensor_n_gs n g = 
     if n=0 then g_1 else
     if n=1 then g else 
                 mtn (n,g)
*)

(* ****************** new and dispose for qbits ******************************* *)

let qcopy (n,v) = (* nobody ought to know about this: I need a .mli for this file *)
  match v with
  | DenseV  v -> n, DenseV (Array.copy v) 
  | SparseV _ -> n,v

let pv_of_braket bks = 
  let rec pv (rm,rv as r) =
    function 
    | bk::bks -> let (m1,v1) = match bk with
                           | Braket.BKZero  -> nv_zero
                           | Braket.BKOne   -> nv_one
                           | Braket.BKPlus  -> nv_plus
                           | Braket.BKMinus -> nv_minus
                 in pv (rprod rm m1, tensor_vv rv v1) bks
    | []      -> r
  in 
  pv nv_1 bks

(* this is in the wrong place *)
let queue_elements queue = Queue.fold (fun es e -> e::es) [] queue

let newqbits, disposeqbits, string_of_qfrees, string_of_qlimbo = (* hide the references *)
  let qbitcount = ref 0 in
  let qfrees = (Queue.create() : qbit Queue.t) in (* for disposed single qbits *)
  let qlimbo = ref [] in (* for disposed entangled bits *)
  let newqbits pn n vopt : qbit list =
    let single () =
      let q =  let fresh () = let q = !qbitcount in qbitcount := q+1; q in
               let tryfrees () = try Queue.take qfrees with Queue.Empty -> fresh() in
               match vopt, !qlimbo with
               | None, _     -> fresh () (* a qbit with symbolic probabilities must be fresh, or
                                            we might re-use symbolic variables which are still in
                                            use. Note this is a space leak, but a small one.
                                            But it makes too many qbits in some demos.
                                            If I could devise a cheap lookup for free variables 
                                            in the qstate, I'd do it.
                                          *)
               | _   , q::qs ->  (match Hashtbl.find qstate q with
                                  | [_],_ -> (* it's a singleton now, we can have it *)
                                             qlimbo := qs; Hashtbl.remove qstate q; q
                                  | _     -> tryfrees ()
                                 )
              | _            -> tryfrees ()
      in
      let vec = match vopt with
                | Some bk  -> bk
                | None     -> if !Settings.symbq then
                                ((* this could be a bug if we used qfrees *)
                                 let pa_sq = Random.float 1.0 in
                                 let pb_sq = 1.0 -. pa_sq in
                                 let ab = sqrt(pa_sq), sqrt(pb_sq) in
                                 make_nv [csnum_of_snum (S_symb {id=q; alpha=false; conj=false; secret=ab}); 
                                          csnum_of_snum (S_symb {id=q; alpha=true;  conj=false; secret=ab})
                                         ] 
                                )
                              else (* random basis, random fixed value *)
                               qcopy (match Random.bool (), Random.bool ()  with
                                      | false, false -> nv_zero 
                                      | false, true  -> nv_one
                                      | true , false -> nv_plus 
                                      | true , true  -> nv_minus
                                     )
      in
      q, vec
    in
    let qsize = match vopt with
                | None       -> 1
                | Some (_,v) -> 
                    try Z.to_int (log_2 (vsize v)) 
                    with Invalid_argument _ ->  
                      raise (Error (Printf.sprintf "ket size %s is not power of 2 in newqbits %s %s %s"
                                      (string_of_zint (vsize v)) pn n
                                      (string_of_option string_of_ket vopt)
                                   )
                            )

    in 
    let qs, qv = match qsize with
                 | 0 -> raise (Error (Printf.sprintf "zero size ket in newqbits %s %s %s" pn n (string_of_option string_of_ket vopt)))
                 | _ -> let qs, vs = Listutils.unzip (Listutils.tabulate qsize (fun _ -> single())) in
                        let qv = qs, List.hd vs in
                        List.iter (fun q -> Hashtbl.add qstate q qv) qs;
                        qs, qv
    in
    if !verbose || !verbose_qsim then
        Printf.printf "%s newqbits %s (%s) -> %s; now %s|->%s\n"
                      (Name.string_of_name pn)
                      (Name.string_of_name n)
                      (string_of_option (string_of_ket) vopt)
                      (string_of_qbits qs)
                      (string_of_qbits qs)
                      (string_of_qval qv);
    qs
  in
  let disposeqbits pn qs = 
    if !verbose || !verbose_qsim then
      Printf.printf "%s disposes %s " (Name.string_of_name pn) (string_of_qbits qs);
    let single q = 
      match Hashtbl.find qstate q with
                        | [q],_ -> Hashtbl.remove qstate q; Queue.add q qfrees;
                                   if !verbose || !verbose_qsim then
                                     Printf.printf "to qfrees %s\n" (bracketed_string_of_list string_of_qbit (queue_elements qfrees))
                        | qv    -> (* don't dispose entangled qbits *)
                                   if !verbose || !verbose_qsim then
                                     Printf.printf "to qlimbo %s\n" (bracketed_string_of_list 
                                                                       (fun q -> Printf.sprintf "%s|->%s"
                                                                                                (string_of_qbit q)
                                                                                                (string_of_qval (Hashtbl.find qstate q))
                                                                       )
                                                                       !qlimbo
                                                                    )
                                                   ;
                                   qlimbo := q::!qlimbo
    in
    List.iter single qs
  in
  let string_of_qfrees () = bracketed_string_of_list string_of_qbit (queue_elements qfrees) in
  let string_of_qlimbo () = bracketed_string_of_list string_of_qbit !qlimbo in
  newqbits, disposeqbits, string_of_qfrees, string_of_qlimbo
  
let strings_of_qsystem () = [Printf.sprintf "qstate=%s" (string_of_qstate ());
                             Printf.sprintf "qfrees=%s" (string_of_qfrees ());
                             Printf.sprintf "qlimbo=%s" (string_of_qlimbo ())
                            ]

(* idx: the index position of q in qs *)
let idx q qs = 
  let rec f i = function
    | q'::qs -> if q = q' then i else f (i+1) qs
    | []     -> raise (Error (Printf.sprintf "** Disaster: %s not in (%s)" 
                                             (string_of_qbit q) 
                                             (string_of_list string_of_qbit "," qs)
                 
                             )
                      )
  in
  f 0 qs

  
(* an n-bit mask, given an index -- in effect 2^n-1*)
let mask n :zint = Z.(z_2**n - z_1)

(* given an index, a one-bit mask to pick it out *)
let onebitmask iq qs :zint = let pos = List.length qs-iq-1 in Z.(z_1 lsl pos)

(* a one-bit mask to pick out q from qs *)
let ibit q qs :zint = let iq = idx q qs in onebitmask iq qs

(* n is destination; iq is where it is. *)
let make_nth qs (vm,vv as v) n iq = 
  let bad s = 
    raise (Disaster (Printf.sprintf "make_nth qs=%s v=%s n=%d iq=%d -- %s"
                                        (bracketed_string_of_list string_of_qbit qs)
                                        (string_of_ket v) n iq s
                    )
          )
  in
  if !verbose || !verbose_qsim then Printf.printf "make_nth qs=%s v=%s n=%d iq=%d "
                                                        (bracketed_string_of_list string_of_qbit qs)
                                                        (string_of_ket v) n iq;
  let nqs = List.length qs in
  if n<0 || n>=nqs then bad "bad n";
  if iq<0 || iq>=nqs then bad "bad iq";
  if iq=n then 
    (if !verbose || !verbose_qsim then Printf.printf "-> (no change)\n";
     qs, v
    )
  else
    (let qmask = onebitmask iq qs in
     let nmask = onebitmask n qs in
     let hdmask, midmask, tlmask =
       let (lsl) = Z.(lsl) in
       if n<iq then (mask n)        lsl (nqs-n),
                    (mask (iq-n))   lsl (nqs-iq),
                    mask (nqs-iq-1)
               else (mask iq)      lsl (nqs-iq),
                    (mask (n-iq))  lsl (nqs-n-1),
                    mask (nqs-n-1)
     in
     (* if !verbose || !verbose_qsim then 
       Printf.printf "qmask %d nmask %d hdmask %d midmask %d tlmask %d\n" 
                      qmask nmask hdmask midmask tlmask;
      *)
     let destn i = Z.(let (<) = Stdlib.(<) in
                      (i land hdmask)                                    lor 
                      (if n<iq then (asr) else (lsl)) (i land midmask) 1 lor 
                      (i land tlmask)                                    lor
                      (if i land qmask<>z_0 then nmask else z_0)
                     )
     in
     let vv' = match vv with
               | DenseV v ->
                   let v' = Array.copy v in
                   let nv = Array.length v in
                   for i=0 to nv-1 do
                     (* if !verbose || !verbose_qsim then Printf.printf "v'.(%d) <- v.(%d)\n" j i; *)
                     v'.(Z.to_int (destn (Z.of_int i))) <- v.(i)
                   done;
                   DenseV v'
               | SparseV (n, cv) -> 
                   let cv' = List.map (fun (i,x) -> destn i, x) cv in
                   SparseV (n, List.sort (fun (i,_) (j,_) -> Z.compare i j) cv') 
     in
     let v' = vm, vv' in
     let qs' =
       if n<iq then let hdseg, tlseg = take n qs, drop n qs in
                    let midseg, tlseg = take (iq-n) tlseg, drop (iq-n) tlseg in
                    let q, tlseg = List.hd tlseg, List.tl tlseg in
                    hdseg@[q]@midseg@tlseg
               else let hdseg, tlseg = take iq qs, drop iq qs in
                    let q, tlseg = List.hd tlseg, List.tl tlseg in
                    let midseg, tlseg = take (n-iq) tlseg, drop (n-iq) tlseg in
                    hdseg@midseg@[q]@tlseg
     in
     if !verbose || !verbose_qsim then Printf.printf "-> qs' %s v' %s\n" 
                                                        (bracketed_string_of_list string_of_qbit qs')
                                                        (string_of_ket v');
     qs', v'
    )
    
let make_first qs v iq = make_nth qs v 0 iq
   
let rotate_left qs v = make_first qs v (List.length qs - 1)

let try_split qs (vm,vv as v) =
  let nqs = List.length qs in
  let nvs = vsize vv in
  let nzs = countzeros_v z_0 nvs vv in
  let worth_a_try = Z.(nzs*z_2>=nvs) in (* and I could do stuff with |+>, |-> as well ... *)
  let rec t_s i qs vv = 
    if i=nqs then None 
    else
      (if !verbose_qcalc then 
         Printf.printf "t_s %s\n" (string_of_qval (qs,(vm,vv)));
       let nh = nvs /: z_2 in
       (* if the first half is all zeros then use nv_one, which is 0+1 *)
       if countzeros_v z_0 nh vv =: nh then
         Some (qs, qcopy nv_one, (vm, vseg nh nvs vv))
       else
       (* if the second half is all zeros then use nv_zero, which is 1+0 *)
       if countzeros_v nh nvs vv =: nh then
         Some (qs, qcopy nv_zero, (vm, vseg z_0 nh vv))
       else
         (let qs, (_,vv) = rotate_left qs (vm,vv) in 
          t_s (i+1) qs vv
         )
      )
  in
  let r = if worth_a_try then t_s 0 qs vv else None in
  if !verbose_qcalc then
    Printf.printf "try_split %s%s (nzs=%s, nvs=%s, worth_a_try=%B) => %s\n" 
                  (string_of_qbits qs) (string_of_ket v)
                  (string_of_zint nzs) (string_of_zint nvs) worth_a_try
                  (string_of_option (fun (qs,k1,k2) -> Printf.sprintf "%s:%s; %s:%s"
                                                                        (string_of_qbit (List.hd qs)) (string_of_ket k1) 
                                                                        (string_of_qbits (List.tl qs)) (string_of_ket k2) 
                                    )
                                    r
                  );
  r
  
let rec record ((qs, vq) as qv) =
   let report () = if !verbose || !verbose_qsim then
                    Printf.printf "recording %s|->%s\n" (match qs with 
                                                         | [q] -> string_of_qbit q
                                                         | _   -> bracketed_string_of_list string_of_qbit qs
                                                        ) 
                                                        (string_of_qval qv)
   in
   let accept q = Hashtbl.replace qstate q qv in
   match qs with
   | []     -> raise (Error (Printf.sprintf "record gets %s" (string_of_qval qv)))
   | [q]    -> accept q
   | _'     -> (* try to split it up *)
               match try_split qs vq with
               | Some (q::qs',v,vq') -> record ([q], v); record (qs', vq')
               | _                   -> report (); List.iter accept qs

let qsort (qs,v) = 
  let qs' = List.sort Stdlib.compare qs in
  let reorder (qs,v) order =
    let reorder (qs,v) (n,q) = make_nth qs v n (idx q qs) in
    List.fold_left reorder (qs,v) order
  in
  reorder (qs,v) (numbered qs')

let ugstep_padded pn qs g gpad = 
  if !verbose || !verbose_qcalc then
    (Printf.printf "ugstep_padded %s %s %s %s\n" 
                    pn 
                    (bracketed_string_of_list (fun q -> string_of_pair string_of_qbit string_of_qval ":" (q,qval q)) qs)
                    (string_of_gate g)
                    (string_of_gate gpad);
     flush_all ()
    );
  if g=g_I && (gpad=g_I || List.length qs=1) then () else 
    (let bad s = raise (Disaster (Printf.sprintf "** ugstep %s %s %s -- %s"
                                                       pn
                                                       (bracketed_string_of_list string_of_qbit qs)
                                                       (string_of_gate g)
                                                       s
                                 )
                       ) 
     in
  
     (* qs must be distinct *)
     let rec check_distinct_qbits = function
       | q::qs -> if List.mem q qs then bad "repeated qbit" else check_distinct_qbits qs
       | []    -> ()
     in
     check_distinct_qbits qs;
  
     (* size of gate must be 2^(length qs) *)
     let nqs = List.length qs in
     let veclength = Z.(z_2**nqs) in
     (* gates are square *)
     if veclength<>:gsize g then bad (Printf.sprintf "qbit/gate mismatch (%d qbits, %s*%s gate)"
                                                                            nqs
                                                                            (string_of_zint (gsize g)) (string_of_zint (gsize g))
                                    );
  
     let show_change qs' v' g' =
       Printf.printf "we took ugstep_padded %s %s %s %s and made %s*(%s,%s)\n"
                           pn
                           (bracketed_string_of_list (fun q -> string_of_pair string_of_qbit string_of_qval ":" (q,qval q)) qs)
                           (string_of_gate g)
                           (string_of_gate gpad)
                           (string_of_gate g')
                           (string_of_qbits qs')
                           (string_of_ket v');
       flush_all ()
     in
  
     (* because of the way qbit state works, values of qbits will either be disjoint or identical *)
     let qs', v' = qval_of_qs qs in
  
     (* now, because of removing duplicates, the qbits may not be in the right order in qs'. So we put them in the right order *)
     (* Now that we have an efficient representation of I⊗⊗n, just put them first *)
     let numbered_qs = Listutils.numbered qs in
     let qs', v' = List.fold_left (fun (qs',v') (n,q) -> make_nth qs' v' n (idx q qs')) (qs',v') numbered_qs in
     
     (* add enough pads to g to deal with v' *)
     let tensor_n_gs n g =
       if n=0 then                     g_1             else
       if n=1 then                     g               else
       if !func_matrices && g=g_I then func_I n        else
       if !func_matrices && g=g_H then func_H n        else
                                       tensor_n_gs n g
     in
     let g' = if g=gpad then tensor_n_gs (List.length qs') g                                   else
                             tensor_gg g (tensor_n_gs (List.length qs' - List.length qs) gpad)
     in
  
     if !verbose || !verbose_qsim || !verbose_qcalc then show_change qs' v' g';
  
     let v'' = mult_gnv g' v' in
     record (qs',v'')
    )

let ugstep pn qs g = ugstep_padded pn qs g g_I

let fp_h2 = 0.5
let fp_h = sqrt fp_h2
let fp_f2 = (1.0 +. fp_h) /. 2.0
let fp_f = sqrt fp_f2
let fp_g2 = (1.0 -. fp_h) /. 2.0
let fp_g = sqrt fp_g2

let rec compute = function
  | S_0         -> 0.0
  | S_1         -> 1.0
  | S_f         -> fp_f
  | S_g         -> fp_g
  | S_h i       -> (match i with
                    | 0             -> 1.0
                    | 1             -> fp_h
                    | _ when i<0    -> 1.0 /. compute (S_h (~-i))
                    | _             -> fp_h2 *. compute (S_h (i-2))
                   )             
  | S_symb symb  -> let a,b = symb.secret in if symb.alpha then b else a
  | S_neg  p     -> ~-. (compute p)
  | S_prod ss    -> List.fold_left ( *. ) 1.0 (List.map compute ss)
  | S_sum  ss    -> List.fold_left ( +. ) 0.0 (List.map compute ss)

let paranoid = false
let _zeroes = ref z_0
let _ones = ref z_0

let rec qmeasure disposes pn gate q = 
  if gate = g_I then (* computational measure *)
    (let qs, (vm,vv as v) = qval q in
     let nv = vsize vv in
     (* make q first in qs: it simplifies life no end *)
     let qs, (_, vv) = make_first qs v (idx q qs) in
     (* probability of measuring 1 is sum of second-half probs *)
     let nvhalf = Z.(nv asr 1) in
     (* the obvious way is to fold sum across the vector. But that leads to nibbling by double 
        ... so we try to do it a more linear (maybe) way 
      *)
     let getsum i n =
       if !verbose || !verbose_qsim then 
         Printf.printf "getsum %s %s " (string_of_zint i) (string_of_zint n);
       let els = match vv with
                 | SparseV (_, cv) -> let lim = i+:n in
                                      let cv' = takewhile (fun (j,_) -> j<:lim) 
                                                          (dropwhile (fun (j,_) -> j<:i) cv)
                                      in
                                      List.map (fun (_,x) -> absq x) cv'
                 | DenseV  dv      -> let i = Z.to_int i in
                                      let n = Z.to_int n in
                                      Listutils.tabulate n (fun j -> absq dv.(i+j)) 
       in
       let r = simplify_sum (sflatten els) in
       if !verbose || !verbose_qsim || !verbose_measure then 
         Printf.printf "%s = %s\n" (bracketed_string_of_list string_of_snum els) (string_of_snum r);
       r
     in
     let prob_1 = getsum nvhalf nvhalf in
     if !verbose || !verbose_qsim || !verbose_measure || paranoid then 
       Printf.printf "%s qmeasure [] %s; %s|->%s; prob_1 = %s;"
                     (Name.string_of_name pn)
                     (string_of_qbit q)
                     (string_of_qbit q)
                     (string_of_qval (qval q))
                     (string_of_snum prob_1);
     (* vv is not normalised: you have to divide everything by vm to get the normalised version. 
        So in finding out whether we have 1 or 0, we have to take the possibility of scoring 
        more or less than vm^2/2.
      *)
     let r = let vm_sq_value = compute vm in
             let prob_value = compute prob_1 in (* squaring has been done *)
             if prob_value=vm_sq_value then 
               (if !verbose || !verbose_qsim || !verbose_measure || paranoid then Printf.printf " that's 1\n";
                1
               ) 
             else
             if prob_value=0.0 then
               (if !verbose || !verbose_qsim || !verbose_measure || paranoid then Printf.printf " that's 0\n";
                0
               ) 
             else
               let rg = Random.float vm_sq_value in
               let r = if rg<prob_value then 1 else 0 in
               if !checkrandombias then
                 (if r=1 then _ones := !_ones +: z_1 else _zeroes := !_zeroes +: z_1);
               if !verbose || !verbose_qsim || !verbose_measure || paranoid then 
                 Printf.printf " test %f<%f %B: choosing %d (%s/%s);\n" rg prob_value (rg<prob_value) r 
                                                                        (string_of_zint !_zeroes) (string_of_zint !_ones);
               r
     in
     (* set the unchosen probs to zero, then normalise *)
     let vv = let lo = if r=1 then z_0    else nvhalf in
              let hi = if r=1 then nvhalf else nv     in
              zeroseg lo hi vv
     in
     let modulus = (* easy when q is first in qs *)
       if r=1 then prob_1 
       else simplify_sum (sflatten [vm; rneg prob_1])
     in 
     if !verbose_qcalc then 
       Printf.printf " (un-normalised %s modulus %s vm_sq %s);" (string_of_qval (qs,v)) (string_of_snum modulus) (string_of_snum vm);
     let vm', vv = 
       match modulus with
       | S_1                -> S_1, vv
       | S_h k  when k mod 2 = 0 
                            -> let n = k/2 in
                               (* multiply by 2**(n/2) *)
                               let vv = _for_fold_left 1 1 n vv (fun vv _ -> map_v (fun x -> csum x x) vv) in
                               (* and then by 1/h if n is odd *)
                               let vv = if n mod 2 = 1 then map_v c_r_div_h vv else vv in
                               S_1, vv
       (* at this point it _could_ be necessary to guess roots of squares. 
        * Or maybe a better solution is required ...
        *)
       | _                  -> 
           (* is there just one possibility? If so, set it to S_1. And note: normalise 1 *)
           if nv -: countzeros_v z_0 nv vv = z_1 then
             let cv = sparse_elements_v vv in
              S_1, SparseV (nv, List.map (fun (i,_) -> (i,c_1)) cv)
           else
             (if !verbose || !verbose_qsim || !verbose_measure || paranoid then
                Printf.printf "\noh dear! q=%d r=%d; was %s snum %s; un-normalised %s modulus %s vm %s\n" 
                                          q r (string_of_qval (qval q)) (string_of_snum prob_1)
                                          (string_of_qval (qs,v)) (string_of_snum modulus) (string_of_snum vm); 
              modulus, vv
             ) 
     in
     let qv = qs, (vm',vv) in
     if !verbose || !verbose_qsim || !verbose_measure then 
       Printf.printf " result %d and %s\n" r (bracketed_string_of_list (fun q -> Printf.sprintf "%s:%s" 
                                                                                     (string_of_qbit q)
                                                                                     (string_of_qval (qval q))
                                                                       ) 
                                                                       qs
                                             );
     record qv; (* which will split it up for us *)
     if disposes then disposeqbits pn [q];
     r
    )
  else (* in gate-defined basis *)
    (if gsize gate <> z_2 then 
       raise (Error (Printf.sprintf "** Disaster: (basis arity) qmeasure %s %s %s"
                                    pn
                                    (string_of_gate gate)
                                    (string_of_qbit q)
                    )
             );
     let gate' = dagger_g gate in  (* cjtransposed gate *)
     let qv = qval q in
     (* first of all rotate with gate' *)
     ugstep_padded pn [q] gate' gate'; 
     let bit = qmeasure disposes pn g_I q in
     (* that _must_ have broken any entanglement: rotate the parts back separately *)
     let rec rotate qs =
       match qs with
       | []    -> () (* done it *)
       | q::qs -> let qqs, qqv = qval q in
                  ugstep_padded pn [q] gate gate;
                  rotate (List.filter (fun q -> not (List.mem q qqs)) qs)
     in
     rotate (List.filter (fun q' -> q'<>q) (fst qv)); 
     (* rotate q as well, if it wasn't disposed *)
     if not disposes then ugstep_padded pn [q] gate gate;
     bit
    )
