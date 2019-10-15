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
open Number (* for num *)

exception Error of string

type qval = qbit list * probvec (* with n qbits, 2^n probs in the array *)

let string_of_qval_full full (qs,v) =
  match full, qs with
  | false, [_] -> string_of_probvec v
  | _          -> Printf.sprintf "[%s]%s"
                          (string_of_list string_of_qbit ";" qs)
                          (string_of_probvec v)
                
let string_of_qval = string_of_qval_full false

let qstate = Hashtbl.create ?random:(Some true) 100 (* 100? a guess *)

let init () = Hashtbl.reset qstate

let string_of_qstate () = 
  let qqvs = Hashtbl.fold (fun q qv ss -> (q,qv) :: ss) qstate []
  in
  Printf.sprintf "{%s}" (string_of_list (string_of_pair string_of_qbit string_of_qval " -> ") "; " (List.sort Pervasives.compare qqvs))

let qval q = try Hashtbl.find qstate q
             with Not_found -> raise (Error (Printf.sprintf "** Disaster: qval with q=%s qstate=%s"
                                                            (string_of_qbit q)
                                                            (string_of_qstate ())
                                            )
                                     )

(* *********************** simplification ************************************ *)

(* The normal form is a sum of possibly-negated products. 
 * Both sums and products are left-recursive.
 * Products are sorted according to the type definition: i.e.
 * P_0, P_1, P_f, P_g, P_h, Psymb. But ... this isn't good enough. 
 
 * We need to sort identifiers according to their suffix: a0,b0,a1,b1, ...
 
 * Pervasives.compare works if we change the definition of Psymb, so I did
 
 *)

(* let compare p1 p2 =
     match p1, p2 with
     | Psymb (b1,q1,_), Psymb (b2,q2,_) -> Pervasives.compare (q1,b1) (q2,b2)
     | _                                -> Pervasives.compare p1      p2
*)
(* we deal with long lists. Avoid sorting if poss *)
let sort compare ps =
  let rec check ps' =
    match ps' with
    | p'::(p''::_ as ps') -> if p'<p'' then check ps' else List.sort compare ps
    | _                   -> ps
  in
  check ps
  
let rec rneg p =
  let r = match p with
          | Pneg p        -> p
          | P_0           -> p
          | Psum ps       -> simplify_sum (List.map rneg ps)
          | _             -> Pneg p
  in
  if !verbose_simplify then
    Printf.printf "rneg (%s) -> %s\n" (string_of_prob p) (string_of_prob r);
  r
    
and rprod p1 p2 =
  let r = match p1, p2 with
          | P_0             , _
          | _               , P_0               -> P_0
          | P_1             , _                 -> p2
          | _               , P_1               -> p1
          | Pneg p1         , _                 -> rneg (rprod p1 p2)
          | _               , Pneg p2           -> rneg (rprod p1 p2)
          | _               , Psum p2s          -> let ps = List.map (rprod p1) p2s in
                                                   simplify_sum (sflatten ps)
          | Psum p1s        , _                 -> let ps = List.map (rprod p2) p1s in
                                                   simplify_sum (sflatten ps)
          | Pprod p1s       , Pprod p2s         -> simplify_prod (p1s @ p2s)
          | _               , Pprod p2s         -> simplify_prod (p1 :: p2s)
          | Pprod p1s       , _                 -> simplify_prod (p1s @ [p2])
          | _                                   -> simplify_prod [p1;p2]
  in
  if !verbose_simplify then
    Printf.printf "rprod (%s) (%s) -> %s\n" (string_of_prob p1) (string_of_prob p2) (string_of_prob r);
  r

(* warning: this can deliver a sum, which mucks up the normal form *)
and simplify_prod ps = (* We deal with constants, f^2, g^2, gh, fg *)
  let r = let rec sp r ps = 
            let premult p ps = 
              let popt, ps = sp r ps in
              (match popt with 
               | Some pre_p -> Some (rprod pre_p p)
               | None       -> Some p
              ), ps
            in
            match ps with
            | P_0            :: ps -> None, [P_0]
            | P_1            :: ps 
            | P_h 0          :: ps -> sp r ps
            | P_f   :: P_f   :: ps -> premult (Psum [P_h 2; P_h 3]) ps
            | P_f   :: P_g   :: ps -> premult (P_h 3) ps
            | P_g   :: P_g   :: ps -> premult (Psum [P_h 2; Pneg (P_h 3)]) ps
(*          | P_g   :: P_h i :: ps    (* prefer f to g: gh^3 is gfg = fg^2 *)
              when i>=3            -> sp (P_f :: r) (P_g :: P_g :: (ihs (i-3) ps)) 
 *)
            | P_g   :: P_h i :: ps'    (* prefer f to g: gh^3 is gfg = fg^2 = f(h^2-h^3) so gh = f(1-h) *)
              when i>=1            -> 
                                      premult (Psum [P_1; Pneg (P_h 1)]) (P_f :: (ihs (i-1) ps'))
            | P_h i :: P_h j :: ps -> sp (ihs (i+j) r) ps
            | p              :: ps -> sp (p::r) ps
            | []                   -> None, List.rev r
          in
          let popt, ps = sp [] (sort Pervasives.compare ps) in
          let p = match ps with 
                  | []  -> P_1
                  | [p] -> p 
                  | _   -> Pprod ps 
          in
          match popt with 
          | Some pre_p -> rprod pre_p p
          | None       -> p
  in
  if !verbose_simplify then
    Printf.printf "simplify_prod %s -> %s\n" (bracketed_string_of_list string_of_prob ps) (string_of_prob r);
  r

and rsum p1 p2 = 
  let r = match p1, p2 with
          | P_0     , _         -> p2
          | _       , P_0       -> p1
          | Psum p1s, Psum p2s  -> simplify_sum (p1s @ p2s)
          | _       , Psum p2s  -> simplify_sum (p1 :: p2s)
          | Psum p1s, _         -> simplify_sum (p1s @ [p2])
          | _                   -> simplify_sum [p1;p2]
  in
  if !verbose_simplify then
    Printf.printf "rsum (%s) (%s) -> %s\n" (string_of_prob p1) (string_of_prob p2) (string_of_prob r);
  r

and sflatten ps = (* flatten a list of sums *)
  let rec sf ps p = 
    match p with
    | Psum ps' -> ps' @ ps
    | _        -> p :: ps
  in
  let r = if List.exists (function Psum _ -> true | _ -> false) ps 
          then List.fold_left sf [] ps   
          else ps
  in
  if !verbose_simplify then
    Printf.printf "sflatten %s -> %s\n" 
                  (bracketed_string_of_list string_of_prob ps) 
                  (bracketed_string_of_list string_of_prob r);
  r

and ihs i ps = if i=0 then ps else P_h i::ps

and simplify_sum ps = 
  let r = let rec scompare p1 p2 = (* ignore negation *)
            match p1, p2 with
            | Pneg p1  , _         -> scompare p1 p2
            | _        , Pneg p2   -> scompare p1 p2
         (* | Pprod p1s, Pprod p2s -> Pervasives.compare p1s p2s *)
            | _                    -> Pervasives.compare p1 p2
          in
          let rec double p1 rest = (* looking for h^2k*X+h^2k*X+.... *)
            (* find the h entry, if any, in p1 *)
            let rec split3 isneg pres ps =
              match ps with 
              | P_h i :: ps -> if i>=2 then Some (isneg, pres, i, ps) else None
              | p     :: ps -> split3 isneg (p::pres) ps
              | []          -> None
            in
            let rec nsplit3 isneg = function
                                    | Pneg p          -> nsplit3 (not isneg) p
                                    | P_h i when i>=2 -> Some (isneg,[],i,[])
                                    | Pprod ps        -> split3 isneg [] ps
                                    | _               -> None
            in
            let r = match nsplit3 false p1 with
                    | Some (isneg,pres,maxi,posts) ->
                        (* i is how many hs we use up, k is 2^(i/2) *)
                        let rec gofor i k rest =
                          let rec takeeqs k rest =
                            match k, rest with
                            | 0, _       -> Some rest
                            | _, p::rest -> if p1=p then takeeqs (k-1) rest else None
                            | _, []      -> None
                          in
                          if i>maxi then None else
                          takeeqs k rest &~~ (fun rest -> gofor (i+2) (k*2) rest
                                                          |~~ (fun _ -> let r = Some ((if isneg then rneg else id)
                                                                                        (simplify_prod (prepend pres (P_h (maxi-i)::posts))),
                                                                                      rest
                                                                                     )
                                                                          in
                                                                          if !verbose_simplify then
                                                                            Printf.printf "gofor %d %d %s (p1=%s)-> %s\n"
                                                                                            i
                                                                                            k
                                                                                            (bracketed_string_of_list string_of_prob rest)
                                                                                            (string_of_prob p1)
                                                                                            (string_of_option (string_of_pair string_of_prob (bracketed_string_of_list string_of_prob) ",") r);
                                                                          r
                                                              )
                                             )
                        in
                        gofor 2 1 rest
                    | _                            -> None
            in
            if !verbose_simplify then
              Printf.printf "double (%s) %s -> %s\n" (string_of_prob p1)  
                                                     (bracketed_string_of_list string_of_prob rest)
                                                     (string_of_option (string_of_pair string_of_prob (bracketed_string_of_list string_of_prob) ",") r);
            r
          in
          let takeit pre post =
            let pre , _ = unzip pre in
            let post, _ = unzip post in
            Some (simplify_prod (pre @ post))
          in
          let partition_1 pps =
            let rec pp_1 r pps =
              match pps with
              | (a,b) as hd :: pps when a=b -> pp_1 (hd::r) pps
              | _                           -> List.rev r, pps
            in
            pp_1 [] pps
          in
          let all_same pps =
            let _, post = partition_1 pps in
            null post
          in
          let rec a2b2 p1 p2 = (* looking for X*a^2+X*b^2 *)
            let r = match p1, p2 with
                    | Pneg p1         , Pneg p2             -> a2b2 p1 p2 &~~ (_Some <.> rneg)
                    | Pprod p1s       , Pprod p2s           ->
                        (try let pps = zip p1s p2s in
                             let pre, rest = partition_1 pps in
                             match rest with
                             | (Psymb (q1, false, _), Psymb (q2, true, _)) ::
                               (Psymb (q3, false, _), Psymb (q4, true, _)) :: post  
                               when q1=q2 && q1=q3 && q1=q4 && all_same post
                                     -> takeit pre post
                             | _     -> None
                         with Zip -> None
                        )
                    | _                                     -> None
            in
            if !verbose_simplify then
              Printf.printf "a2b2 (%s) (%s) -> %s\n" (string_of_prob p1)  
                                                     (string_of_prob p2)
                                                     (string_of_option string_of_prob r);
            r
          in
          let rec sp again r ps =
            match ps with
            | P_0                :: ps            -> sp again r ps
            | P_1     :: Pneg (P_h k as p) 
                                 :: ps when k>0 && k mod 2=0
                                                  -> sp true (prepend (tabulate ((1 lsl (k/2)) - 1) (const p)) r) ps
            | Pneg p1 :: p2      :: ps when p1=p2 -> sp again r ps
            | p1      :: Pneg p2 :: ps when p1=p2 -> sp again r ps
            | p1      :: p2      :: ps when p1=p2 -> (match double p1 (p2::ps) with
                                                      | Some (p,ps) -> sp true (p::r) ps
                                                      | None        -> sp again (p1::r) (p2::ps)
                                                     )
            (* the next lot are because h^j-h^(j+2) = h^j(1-h^2) = h^(j+2) 
               If it all works then we should allow also for j=0, and the whole mess
               prefixed with f (but not g, because of simplify_prod).
             *)
            | Pprod (P_h j :: p1s)        :: Pneg (Pprod (P_h k :: p2s) as p2) :: ps
                   when k=j+2 && p1s=p2s
                                                  -> sp true (p2::r) ps
            | Pneg (Pprod (P_h j :: p1s)) :: (Pprod (P_h k :: p2s) as p2)      :: ps
                   when k=j+2 && p1s=p2s
                                                  -> sp true (Pneg p2::r) ps
            | Pprod (P_h j :: p1s)        :: p2 :: Pneg (Pprod (P_h k :: p3s) as p3) :: ps
                   when k=j+2 && p1s=p3s
                                                  -> sp true r (p2::p3::ps)
            | Pneg (Pprod (P_h j :: p1s)) :: p2 :: (Pprod (P_h k :: p3s) as p3)      :: ps
                   when k=j+2 && p1s=p3s
                                                  -> sp true r (p2::Pneg p3::ps)
            | p1      :: p2      :: ps            -> (match a2b2 p1 p2 with
                                                      | Some p -> sp true (p::r) ps
                                                      | None   -> sp again (p1::r) (p2::ps)
                                                     )
            | p                  :: ps            -> sp again (p::r) ps
            | []                                  -> let r = List.rev r in
                                                    if again then doit (sflatten r) else r
          and doit ps = sp false [] (sort scompare ps)
          in
          if List.exists (function Psum _ -> true | Pneg (Psum _) -> true | _ -> false) ps then
            raise (Error (Printf.sprintf "simplify_sum (%s)" (string_of_prob (Psum ps))))
          else
          match doit ps with
          | []  -> P_0
          | [p] -> p
          | ps  -> Psum ps
  in
  if !verbose_simplify then
    Printf.printf "simplify_sum (%s) -> %s\n" (string_of_prob (Psum ps)) (string_of_prob r);
  r

and sqrt_half i =   (* (1/sqrt 2)**i *)
  let r = if i=0 then P_1 else P_h i in
  if !verbose_simplify then
    Printf.printf "sqrt_half %d -> %s\n" i (string_of_prob r);
  r

(* warning: this can deliver a sum *)
and rdiv_h p = (* multiply by sqrt 2 (= divide by h). Happens: see normalise *)
  let r = match p with
          | P_0                              -> p
          | Pneg p                           -> rneg (rdiv_h p)
          | P_h i                  when i>=1 -> sqrt_half (i-1)
          | Pprod (     P_h i::ps) when i>=1 -> simplify_prod (     sqrt_half (i-1) :: ps)
          | Pprod (P_f::P_h i::ps) when i>=1 -> simplify_prod (P_f::sqrt_half (i-1) :: ps)
          | Pprod (P_g::P_h i::ps) when i>=1 -> simplify_prod (P_g::sqrt_half (i-1) :: ps)
          | Psum  ps                         -> simplify_sum  (sflatten (List.map rdiv_h ps)) (* sflatten because we can get a sum ... *)
          | _                                -> (* p/h = (ph^2+ph^2)/h = ph+ph *)
                                                let ph = rprod p (P_h 1) in
                                                rsum ph ph
  in
  if !verbose_simplify then
    Printf.printf "rdiv_h (%s) -> %s\n" (string_of_prob p) (string_of_prob r);
  r

and rdiv p1 p2 = (* happens in normalise *) (* this needs work for division by sums and also for division by products *)
  let bad () = 
    raise (Error (Printf.sprintf "rdiv (%s) (%s)" (string_of_prob p1) (string_of_prob p2)))
  in
  let r = match p1 with
          | P_0               -> P_0
          | _ when p1=p2      -> P_1
          | Pneg p1           -> rneg (rdiv p1 p2)
          | Pprod ps          -> let rec del ps =
                                   match ps with
                                   | [] -> bad()
                                   | p::ps -> if p=p2 then ps else p::del ps
                                 in
                                 Pprod (del ps)
          | Psum ps           -> simplify_sum (List.map (fun p -> rdiv p p2) ps)
          | _                 -> bad ()
  in
  if !verbose_simplify then
    Printf.printf "rdiv (%s) (%s) -> %s\n" (string_of_prob p1) (string_of_prob p2) (string_of_prob r);
  r
  
(* *********************** complex arith in terms of reals ************************************ *)


let cprod (C (x1,y1)) (C (x2,y2)) = 
  match y1, y2 with
  | P_0, P_0 -> C (rprod x1 x2, P_0)            (* real*real *)
  | P_0, _   -> C (rprod x1 x2, rprod x1 y2)    (* real*complex *)
  | _  , P_0 -> C (rprod x1 x2, rprod y1 x2)    (* complex*real *)
  | _        -> C (rsum (rprod x1 x2) (rneg (rprod y1 y2)), rsum (rprod x1 y2) (rprod y1 x2))

let csum  (C (x1,y1)) (C (x2,y2)) = C (rsum x1 x2, rsum y1 y2)
let cneg  (C (x,y))               = C (rneg x, rneg y)

let cconj (C (x,y))               = C (x, rneg y)

let absq  (C (x,y))               = rsum (rprod x x) (rprod y y)

let c_r_div   (C(x,y)) z          = C (rdiv x z, rdiv y z)
let c_r_div_h (C(x,y))            = C (rdiv_h x, rdiv_h y)

(* we memoise these things ... *)

module OrderedC = struct type t = cprob 
                         let compare = Pervasives.compare
                         let to_string = string_of_cprob
                  end
module CMap = MyMap.Make (OrderedC)
let memofunC f s = CMap.memofun id (fun c -> if !verbose || !verbose_qcalc then Printf.printf "%s (%s)\n" s (string_of_cprob c); f c)

module OrderedC2 = struct type t = cprob*cprob 
                         let compare = Pervasives.compare
                         let to_string = bracketed_string_of_pair string_of_cprob string_of_cprob
                  end
module C2Map = MyMap.Make (OrderedC2)
let memofunC2 f s = 
  curry2 (C2Map.memofun id (uncurry2 (fun c1 c2 -> if !verbose || !verbose_qcalc then 
                                                     Printf.printf "%s (%s) (%s)\n" 
                                                                   s (string_of_cprob c1) (string_of_cprob c2);
                                                   f c1 c2
                                      )
                           )
         )
module OrderedCP = struct type t = cprob*prob 
                         let compare = Pervasives.compare
                         let to_string = bracketed_string_of_pair string_of_cprob string_of_prob
                  end
module CPMap = MyMap.Make (OrderedCP)
let memofunCP f s = 
  curry2 (CPMap.memofun id (uncurry2 (fun c p -> if !verbose || !verbose_qcalc then 
                                                   Printf.printf "%s (%s) (%s)\n" 
                                                                 s (string_of_cprob c) (string_of_prob p);
                                                 f c p
                                    )
                           )
         )

let mcprod = memofunC2 cprod "cprod"
let cprod (C (x1,y1) as c1) (C (x2,y2) as c2) = 
  match x1,y1, x2,y2 with
  | P_0     , P_0, _       , _    
  | _       , _  , P_0     , P_0       -> c_0
  | P_1     , P_0, _       , _         -> c2  
  | _       , _  , P_1     , P_0       -> c1
  | Pneg P_1, P_0, _       , _         -> cneg c2  
  | _       , _  , Pneg P_1, P_0       -> cneg c1
  | _                                  -> mcprod c1 c2
  
let mcsum = memofunC2 csum "csum"
let csum  (C (x1,y1) as c1) (C (x2,y2) as c2) = 
  match x1,y1, x2,y2 with
  | P_0, P_0, _  , _    -> c2 
  | _  , _  , P_0, P_0  -> c1
  | _                   -> mcsum c1 c2
  
(* let cneg = memofunC cneg "cneg" -- possibly not worth it *)
(* let cconj = memofunC cconj "cconj" -- not worth it *)
let absq = memofunC absq "absq"

let c_r_div = memofunCP c_r_div "c_r_div"
let c_r_div_h = memofunC c_r_div_h "c_r_div_h"

(* from here on down, I just assume (hope) that we are working with square matrices *)
(* maybe later that typechecking trick ... *)

let new_v n = Array.make n c_0
let new_ug n = Array.make_matrix n n c_0

let bigI n = let m = Array.make_matrix n n c_0 in
             _for 0 1 n (fun i -> m.(i).(i) <- c_1);
             m
             
let tensor_vv vA vB =
  let nA = vsize vA in
  let nB = vsize vB in
  let vR = new_v (nA*nB) in
  _for 0 1 nA (fun i -> _for 0 1 nB (fun j -> vR.(i*nB+j) <- cprod vA.(i) vB.(j)));
  vR
  
let tensor_qq (mA,vA) (mB,vB) =
  let mR = match mA,mB with
           | P_1, _   -> mB
           | _  , P_1 -> mA
           | _        -> rprod mA mB
  in
  let vR = tensor_vv vA vB in
  if !verbose_qcalc then Printf.printf "%s (><) %s -> %s\n"
                                       (string_of_probvec (mA,vA))
                                       (string_of_probvec (mB,vB))
                                       (string_of_probvec (mR,vR));
  mR,vR
  
let tensor_gg gA gB =
  if !verbose_qcalc then Printf.printf "tensor_gg %s %s = " (string_of_gate gA) (string_of_gate gB);
  let nA = gsize gA in
  let nB = gsize gB in
  let g = if gA=g_1 then gB else
          if gB=g_1 then gA else
            (match gA, gB with
             | DGate dA, DGate dB -> DGate (tensor_vv dA dB)
             | _                  ->
                 let mA = cpaa_of_gate gA in
                 let mB = cpaa_of_gate gB in
                 let mt = new_ug (nA*nB) in
                 _for 0 1 nA (fun i -> 
                                _for 0 1 nA (fun j -> 
                                               let aij = mA.(i).(j) in
                                               _for 0 1 nB (fun m ->
                                                              _for 0 1 nB (fun p ->
                                                                             mt.(i*nB+m).(j*nB+p) <- cprod aij (mB.(m).(p))
                                                                          )
                                                           )
                                            )
                             );
                 gate_of_cpaa mt
            )  
  in
  if !verbose_qcalc then Printf.printf "%s\n" (string_of_gate g);
  g

let tensor_n_gs n g = 
  if n=0 then g_1 else
  if n=1 then g else
              List.fold_left tensor_gg g (Listutils.tabulate (n-1) (const g))
              
(* (* I thought this might be quicker than folding, but it isn't *)
   let rec tensor_n_gs n g =
     if n=0 then g_1 else
     if n=1 then g else
                 let g' = tensor_n_gs (n/2) (tensor_gg g g) in 
                 if n mod 2 = 1 then tensor_gg g' g else g'
*)

(* (* memoised seems to make very little difference, or make it worse *)
   module OrderedNG = struct type t = int*gate 
                             let compare = Pervasives.compare
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

let rowcolprod n row col =
  let de_C (C (x,y)) = x,y in
  let els = Listutils.tabulate n (fun j -> de_C (cprod (row j) (col j))) in
  let reals, ims = List.split els in
  C (simplify_sum (sflatten reals), simplify_sum (sflatten ims))  

let mult_gv g (vm,vv as v) =
  if !verbose_qcalc then Printf.printf "mult_gv %s %s = " (string_of_gate g) (string_of_probvec v);
  let n = Array.length vv in
  if gsize g <> n then
    raise (Error (Printf.sprintf "** Disaster (size mismatch): mult_gv %s %s"
                                 (string_of_gate g)
                                 (string_of_probvec v)
                 )
          );
  let v' = vm, match g with
               | MGate m -> Array.init n (fun i -> let row = m.(i) in rowcolprod n (fun j -> row.(j)) (fun j -> vv.(j)))
               | DGate d -> Array.init n (fun i -> cprod d.(i) vv.(i))
  in
  if !verbose_qcalc then Printf.printf "%s\n" (string_of_probvec v');
  v'
               
let mult_gg gA gB = 
  if !verbose_qcalc then Printf.printf "mult_gg %s %s = " (string_of_gate gA) (string_of_gate gB);
  let n = gsize gA in
  if n <> gsize gB then (* our gates are square *)
    raise (Error (Printf.sprintf "** Disaster (size mismatch): mult_gg %s %s"
                                 (string_of_gate gA)
                                 (string_of_gate gB)
                 )
          );
  let g = match gA, gB with
          | DGate dA, DGate dB -> DGate (Array.init n (fun i -> cprod dA.(i) dB.(i)))
          | _                  ->
              let mA = cpaa_of_gate gA in   
              let mB = cpaa_of_gate gB in
              let m' = new_ug n in
              _for 0 1 n (fun i ->
                            (_for 0 1 n (fun j ->
                                           m'.(i).(j) <- let row = mA.(i) in rowcolprod n (fun k -> row.(k)) (fun k -> mB.(k).(j))
                                        )
                            )
                         );
              gate_of_cpaa m' 
  in
  if !verbose_qcalc then Printf.printf "%s\n" (string_of_gate g);
  g

(* conjugate transpose: transpose and piecewise complex conjugate *)
let dagger g = 
  if !verbose_qcalc then Printf.printf "dagger %s = " (string_of_gate g);
  let n = gsize g in
  let g' = match g with
           | DGate d -> DGate (Array.init n (fun i -> cconj d.(i)))
           | MGate m ->
               let m' = new_ug n in
               _for 0 1 n (fun i ->
                             _for 0 1 n (fun j -> m'.(i).(j) <- cconj (m.(j).(i)))
                          );
               gate_of_cpaa m' 
  in
  if !verbose_qcalc then Printf.printf "%s\n" (string_of_gate g');
  g'
  
(* ****************** new and dispose for qbits ******************************* *)

let qcopy (n,v) = n, Array.copy v (* nobody ought to know about this: I need a .mli for this file *)

let newqbit, disposeqbit, string_of_qfrees, string_of_qlimbo = (* hide the references *)
  let qbitcount = ref 0 in
  let qfrees = ref [] in
  let qlimbo = ref [] in
  let newqbit pn n vopt =
    let q = match !qfrees, vopt with
      | q::qs, Some _ -> qfrees:=qs; q (* only re-use qbits when we don't make symbolic probabilities *)
                                       (* note this is a space leak, but a small one *)
                                       (* but it's a nasty one, because it makes too many qbits in some demos.
                                          if I could devise a cheap lookup for free variables in the qstate, I'd do it.
                                        *)
      | _             -> let q = !qbitcount in 
                         qbitcount := q+1; 
                         q
    in
    let vec = match vopt with
              | Some Basisv.BVzero  -> qcopy v_zero
              | Some Basisv.BVone   -> qcopy v_one
              | Some Basisv.BVplus  -> qcopy v_plus
              | Some Basisv.BVminus -> qcopy v_minus
              | None                -> if !Settings.symbq then
                                         ((* this could be a bug if we used qfrees *)
                                          let pa_sq = Random.float 1.0 in
                                          let pb_sq = 1.0 -. pa_sq in
                                          make_v (List.map c_of_p [Psymb (q, false, sqrt(pa_sq)); Psymb (q, true, sqrt(pb_sq))]) 
                                         )
                                       else (* random basis, random fixed value *)
                                        qcopy (match Random.bool (), Random.bool ()  with
                                               | false, false -> v_zero 
                                               | false, true  -> v_one
                                               | true , false -> v_plus 
                                               | true , true  -> v_minus
                                              )
    in
    let qv = [q],vec in
    Hashtbl.add qstate q qv;
    if !verbose || !verbose_qsim then
      Printf.printf "%s newqbit %s (%s) -> %s; now %s|->%s\n"
                    (Name.string_of_name pn)
                    (Name.string_of_name n)
                    (string_of_option Basisv.string_of_basisv vopt)
                    (string_of_qbit q)
                    (string_of_qbit q)
                    (string_of_qval qv);
    q
  in
  let disposeqbit pn q = 
    if !verbose || !verbose_qsim then
      Printf.printf "%s disposes %s " (Name.string_of_name pn) (string_of_qbit q);
    match Hashtbl.find qstate q with
                      | [q],_ -> Hashtbl.remove qstate q; qfrees := q::!qfrees;
                                 if !verbose || !verbose_qsim then
                                   Printf.printf "to qfrees %s\n" (bracketed_string_of_list string_of_qbit !qfrees)
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
  let string_of_qfrees () = bracketed_string_of_list string_of_qbit !qfrees in
  let string_of_qlimbo () = bracketed_string_of_list string_of_qbit !qlimbo in
  newqbit, disposeqbit, string_of_qfrees, string_of_qlimbo
  
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

(* given an index, a mask to pick it out *)
let bitmask iq qs = 1 lsl (List.length qs-iq-1)

(* a single-bit mask to pick out q from qs *)
let ibit q qs = 
  let iq = idx q qs in
  bitmask iq qs

(* an n-bit mask, given an index *)
let mask n = 
  let rec f m i =
    if i=0 then m else f ((m lsl 1) lor 1) (i-1)
  in
  f 0 n

(* n is destination; iq is where it is. *)
let make_nth qs (vm,vv as v) n iq = 
  let bad s = 
    raise (Disaster (Printf.sprintf "make_nth qs=%s v=%s n=%d iq=%d -- %s"
                                        (bracketed_string_of_list string_of_qbit qs)
                                        (string_of_probvec v)
                                        n
                                        iq
                                        s
                    )
          )
  in
  if !verbose || !verbose_qsim then Printf.printf "make_nth qs=%s v=%s n=%d iq=%d "
                                                        (bracketed_string_of_list string_of_qbit qs)
                                                        (string_of_probvec v)
                                                        n
                                                        iq;
  let nqs = List.length qs in
  if n<0 || n>=nqs then bad "bad n";
  if iq<0 || iq>=nqs then bad "bad iq";
  let nv = vsize vv in
  if iq=n then 
    (if !verbose || !verbose_qsim then
       Printf.printf "-> (no change)\n";
     qs, v
    )
  else
    (let qmask = bitmask iq qs in
     let nmask = bitmask n qs in
     let hdmask, midmask, tlmask =
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
     let vv' = Array.copy vv in
     for i=0 to nv-1 do
       let j = (i land hdmask)                                    lor 
               (if n<iq then (lsr) else (lsl)) (i land midmask) 1 lor 
               (i land tlmask)                                    lor
               (if i land qmask<>0 then nmask else 0)
       in
       (* if !verbose || !verbose_qsim then Printf.printf "v'.(%d) <- v.(%d)\n" j i; *)
       vv'.(j) <- vv.(i)
     done;
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
                                                        (string_of_probvec v');
     qs', v'
    )
    
let make_first qs v iq = make_nth qs v 0 iq
   
let rotate_left qs v = make_first qs v (List.length qs - 1)

let try_split qs (vm,vv as v) =
  let nqs = List.length qs in
  let nvs = Array.length vv in
  let nzs = _for_leftfold 0 1 nvs (fun i nzs -> if vv.(i)=c_0 then nzs+1 else nzs) 0 in
  let worth_a_try = nzs*2>=nvs in (* and I could do stuff with +, - as well ... *)
  let rec t_s i qs vv = 
    if i=nqs then None 
    else
      (if !verbose_qcalc then 
         Printf.printf "t_s %s\n" (string_of_qval (qs,(vm,vv)));
       let n = vsize vv in
       let nh = n / 2 in
       (* if the first half is all zeros then use v_one, which is 0+1 *)
       if _for_all 0 1 nh (fun i -> vv.(i)=c_0) then
         Some (qs, qcopy v_one, (vm,Array.init nh (fun i -> vv.(nh+i))))
       else
       (* if the second half is all zeros then use v_zero, which is 1+0 *)
       if _for_all nh 1 n (fun i -> vv.(i)=c_0) then
         Some (qs, qcopy v_zero, (vm,Array.init nh (fun i -> vv.(i))))
       else
         (let qs, (_,vv) = rotate_left qs (vm,vv) in 
          t_s (i+1) qs vv
         )
      )
  in
  let r = if worth_a_try then t_s 0 qs vv else None in
  if !verbose_qcalc then
    Printf.printf "try_split %s (nzs=%d, nvs=%d, worth_a_try=%B) => %s\n" 
                  (string_of_probvec v)
                  nzs nvs worth_a_try
                  (string_of_option (string_of_triple (bracketed_string_of_list string_of_qbit)
                                                      string_of_probvec 
                                                      string_of_probvec 
                                                      ","
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
  let qs = List.sort Pervasives.compare qs in
  let reorder (qs,v) order =
    let reorder (qs,v) (n,q) = make_nth qs v n (idx q qs) in
    List.fold_left reorder (qs,v) order
  in
  reorder (qs,v) (numbered qs)

let ugstep_padded pn qs g gpad = 
  if g=g_I && List.length qs=1 then () else 
    ((* let noway s = Printf.printf "can't yet handle %s %s\n" (id_string ()) s in *)
     let bad s = raise (Disaster (Printf.sprintf "** ugstep %s %s %s -- %s"
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
     let veclength = 1 lsl nqs in
     if veclength=0 then bad "far too many qbits";
     (* I think our matrices are always square: we start with square gates and multiply and/or tensor *)
     if veclength<>gsize g then bad (Printf.sprintf "qbit/gate mismatch (should be %d columns for %d qbits)"
                                                       veclength
                                                       nqs
                                    );
  
     let show_change qs' v' g' =
       Printf.printf "we took ugstep_padded %s %s %s %s and made %s*(%s,%s)\n"
                                   pn
                                   (bracketed_string_of_list (fun q -> Printf.sprintf "%s:%s" 
                                                                           (string_of_qbit q)
                                                                           (string_of_qval (qval q))
                                                             ) 
                                                             qs
                                   )
                                   (string_of_gate g)
                                   (string_of_gate gpad)
                                   (string_of_gate g')
                                   (bracketed_string_of_list string_of_qbit qs')
                                   (string_of_probvec v')
     in
  
     (* because of the way qbit state works, values of qbits will either be disjoint or identical *)
     let qvals = Listutils.mkset (List.map qval qs) in
     let qss, vs = List.split qvals in
     let qs', v' = List.concat qss, List.fold_left tensor_qq v_1 vs in
  
     (* now, because of removing duplicates, the qbits may not be in the right order in qs'. So we put them in the right order *)
     (* But we don't want to do this too enthusiastically ... *)
     let rec together ilast qs (qs',v') =
       match qs with 
       | []     -> ilast, qs', v'
       | q::qs -> let iq = idx q qs' in
                   let iq' = if iq<ilast then ilast else ilast+1 in
                   together iq' qs (make_nth qs' v' iq' iq) 
     in
     let ilast, qs', v' = together (idx (List.hd qs) qs') (List.tl qs) (qs',v')  in
     let ifirst = idx (List.hd qs) qs' in
  
     (* add enough pads to g to deal with v *)
     let g' = if g=gpad then tensor_n_gs (List.length qs') g else
                             (let pre = tensor_n_gs ifirst gpad in
                              let post = tensor_n_gs (List.length qs'-1-ilast) gpad in
                              tensor_gg pre (tensor_gg g post)
                             )  
     in
  
     if !verbose || !verbose_qsim then show_change qs' v' g';
  
     let v'' = mult_gv g' v' in
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
  | P_0         -> 0.0
  | P_1         -> 1.0
  | P_f         -> fp_f
  | P_g         -> fp_g
  | P_h i       -> (match i with
                    | 0             -> 1.0
                    | 1             -> fp_h
                    | _ when i<0    -> 1.0 /. compute (P_h (~-i))
                    | _             -> fp_h2 *. compute (P_h (i-2))
                   )             
  | Psymb (_,_,r)     -> r
  | Pneg  p     -> ~-. (compute p)
  | Pprod ps    -> List.fold_left ( *. ) 1.0 (List.map compute ps)
  | Psum  ps    -> List.fold_left ( +. ) 0.0 (List.map compute ps)

let paranoid = false
let _zeroes = ref zero
let _ones = ref zero

let rec qmeasure disposes pn gate q = 
  if gate = g_I then (* computational measure *)
    (let qs, (vm,vv as v) = qval q in
     let nv = vsize vv in
     (* make q first in qs: it simplifies life no end *)
     let qs, (_, vv) = make_first qs v (idx q qs) in
     (* probability of measuring 1 is sum of second-half probs *)
     let nvhalf = nv/2 in
     (* the obvious way is to fold sum across the vector. But that leads to nibbling by double 
        ... so we try to do it a more linear (maybe) way 
      *)
     let getsum i n =
       if !verbose || !verbose_qsim then 
         Printf.printf "getsum %d %d " i n;
       let els = Listutils.tabulate n (fun j -> absq vv.(i+j)) in
       let r = simplify_sum (sflatten els) in
       if !verbose || !verbose_qsim then 
         Printf.printf "%s = %s\n" (bracketed_string_of_list string_of_prob els) (string_of_prob r);
       r
     in
     let prob = 
       (* _for_leftfold nvhalf 1 nv (fun i -> rsum (absq vv.(i))) P_0 *) getsum nvhalf nvhalf
     in
     if !verbose || !verbose_qsim || paranoid then 
       Printf.printf "%s qmeasure [] %s; %s|->%s; prob |1> = %s;"
                     (Name.string_of_name pn)
                     (string_of_qbit q)
                     (string_of_qbit q)
                     (string_of_qval (qval q))
                     (string_of_prob prob);
     (* vv is not normalised: you have to divide everything by vm to get the normalised version. 
        So in finding out whether we have 1 or 0, we have to take the possibility of scoring 
        more or less than vm^2/2.
      *)
     let r = let vm_sq_value = compute vm in
             let prob_value = compute prob in (* squaring has been done *)
             if prob_value=vm_sq_value then 
               (if !verbose || !verbose_qsim || paranoid then Printf.printf " that's 1\n";
                1
               ) 
             else
             if prob_value=0.0 then
               (if !verbose || !verbose_qsim || paranoid then Printf.printf " that's 0\n";
                0
               ) 
             else
               let rg = Random.float vm_sq_value in
               let r = if rg<prob_value then 1 else 0 in
               if !checkrandombias then
                 (if r=1 then _ones := !_ones +/ one else _zeroes := !_zeroes +/ one);
               if !verbose || !verbose_qsim || paranoid then 
                 Printf.printf " test %f<%f %B: choosing %d (%s/%s);\n" rg prob_value (rg<prob_value) r (string_of_num !_zeroes) (string_of_num !_ones);
               r
     in
     (* set the unchosen probs to zero, then normalise. *)
     _for (if r=1 then 0 else nvhalf) 1 (if r=1 then nvhalf else nv) (fun i -> vv.(i) <- c_0);
     let modulus = (* easy when q is first in qs *)
       if r=1 then prob 
       else (*_for_leftfold 0 1 nvhalf (fun i -> rsum (absq vv.(i))) P_0*) 
            (* getsum 0 nvhalf *) 
            simplify_sum (sflatten [vm; rneg prob])
     in 
     if !verbose_qcalc then 
       Printf.printf " (un-normalised %s modulus %s vm_sq %s);" (string_of_qval (qs,v)) (string_of_prob modulus) (string_of_prob vm);
     let vm' = 
       match modulus with
       | P_1                -> P_1
       | P_h k  when k mod 2 = 0 
                            -> let n = k/2 in
                               (* multiply by 2**(n/2) *)
                               _for 0 1 (n/2) (fun _ -> _for 0 1 nv (fun i -> vv.(i) <- csum vv.(i) vv.(i)));
                               (* and then by 1/h if n is odd *)
                               if n mod 2 = 1 then
                                 _for 0 1 nv (fun i -> vv.(i) <- c_r_div_h vv.(i));
                               P_1
       | Pprod [p1;p2] when p1=p2 
                            -> _for 0 1 nv (fun i -> vv.(i) <- c_r_div vv.(i) p1);
                               P_1
       (* at this point it _could_ be necessary to guess roots of squares. 
        * Or maybe a better solution is required ...
        *)
       | _                  -> 
           (* is there just one possibility? If so, set it to P_1. And note: normalise 1 *)
           let nzs = List.map (fun p -> if p<>c_0 then 1 else 0) (Array.to_list vv) in
           if List.fold_left (+) 0 nzs = 1 then
             (_for 0 1 nv (fun i -> if vv.(i)<>c_0 then vv.(i)<-c_1);
              P_1
             )
           else
             (if !verbose || !verbose_qsim || paranoid then
                Printf.printf "\noh dear! q=%d r=%d; was %s prob %s; un-normalised %s modulus %s vm %s\n" 
                                          q r (string_of_qval (qval q)) (string_of_prob prob)
                                          (string_of_qval (qs,v)) (string_of_prob modulus) (string_of_prob vm); 
              modulus
             ) 
     in
     let qv = qs, (vm',vv) in
     if !verbose || !verbose_qsim then 
       Printf.printf " result %d and %s\n" r (bracketed_string_of_list (fun q -> Printf.sprintf "%s:%s" 
                                                                                     (string_of_qbit q)
                                                                                     (string_of_qval (qval q))
                                                                       ) 
                                                                       qs
                                             );
     record qv; (* which will split it up for us *)
     if disposes then disposeqbit pn q;
     r
    )
  else (* in gate-defined basis *)
    (if gsize gate <> 2 then 
       raise (Error (Printf.sprintf "** Disaster: (arity) qmeasure %s %s %s"
                                    pn
                                    (string_of_gate gate)
                                    (string_of_qbit q)
                    )
             );
     let gate' = dagger gate in  (* cjtransposed gate *)
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
