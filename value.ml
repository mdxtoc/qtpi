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
open Listutils
open Functionutils
open Optionutils
open Tupleutils
open Braket
open Number
open Name
open Process
open Pattern
open Monenv

exception Disaster of string
exception Error of string

let vsize = Array.length

let _for i inc n f = (* n is size, so up to n-1 *)
  let rec rf i =
    if i<n then (f i; rf (i+inc)) (* else skip *)
  in
  rf i
  
let _for_leftfold i inc n f v =
  let rec ff i v =
    if i<n then ff (i+inc) (f i v) else v
  in
  ff i v

let rec _for_rightfold i inc n f v =
  let rec ff i v =
    if i<n then f i (ff (i+inc) v) else v
  in
  ff i v

let _for_all i inc n f = 
  let rec ff i =
    i=n || (f i && ff (i+inc))
  in
  ff i 
  
let _for_exists i inc n f v = 
  let rec ff i =
    i<n && (f i || ff (i+inc))
  in
  ff i 
  
let queue_elements q = let vs = Queue.fold (fun vs v -> v::vs) [] q in
                       List.rev vs

let string_of_queue string_of sep q = 
  let vs = queue_elements q in
  "{" ^ string_of_list string_of sep vs ^ "}"

type value =
  | VUnit
  | VBit of bool
  | VNum of num
  | VBool of bool
  | VChar of char
  | VBra of bra
  | VKet of ket
  | VGate of gate
  | VString of string
  | VQbit of qbit
  | VQstate of string
  | VChan of chan
  | VTuple of value list
  | VList of value list
  | VFun of (value -> value)        (* with the environment baked in for closures *)
  | VProcess of name * env ref * name list * process

(* h = sqrt (1/2) = cos (pi/4) = sin (pi/4); useful for rotation pi/4, or 45 degrees;
   f = sqrt ((1+h)/2) = cos (pi/8); useful for rotation pi/8 or 22.5 degrees;
   g = sqrt ((1-h)/2) = sin (pi/8); the partner of h;
   
   Note h^2 = 1/2; 
        f^2 = (1+h)/2 = h^2(1+h) = h^2+h^3;
        g^2 = (1-h)/2 = h^2(1-h) = h^2-h^3;
        fg  = sqrt ((1-h^2)/4) = sqrt(1/8) = sqrt(h^6) = h^3  
        
   Also f^2+g^2 = 1 (which will fall out of the above)
 *)
and prob = 
  | P_0
  | P_1
  | P_f              
  | P_g 
  | P_h of int              
  | Psymb of int * bool * float     (* k, false=a_k, true=b_k, both random floats s.t. a_k**2+b_k**2 = 1; random r s.t. 0<=r<=1.0 *)
  | Pneg of prob
  | Pprod of prob list              (* associative *)
  | Psum of prob list               (* associative *)

and cprob = C of prob*prob (* complex prob A + iB *)

and modulus = prob

and probvec = modulus * cprob array (* modulus, vector: written as 1/sqrt(modulus)(vec) *)

and gate = 
    | MGate of cprob array array   (* square matrix *)
    | DGate of cprob array         (* diagonal matrix *)

and qbit = int

(* the gsum_info in channel waiter queues is to deal with guarded sums: an offer
   to communicate is withdrawn from all guards by setting the shared boolean to false.
   The channel list is to remove a space leak (blush): clear out the dead from those channels.
   The space leak is because we keep a set stuck_chans (a set?) for diagnostic printing purposes.
 *)
 
and chan = {cname: int; traced: bool; stream: value Queue.t; wwaiters: (wwaiter*gsum_info) PQueue.t; rwaiters: (rwaiter*gsum_info) PQueue.t}

and gsum_info = (bool * chan list) ref

and runner = name * process * env

and rwaiter = name * pattern * process * env

and wwaiter = name * value * process * env

and env = value monenv (* which, experiment suggests, is more efficient than Map at runtime *)

let gsize = function
  | MGate m -> vsize m  (* assuming square gates *)
  | DGate v -> vsize v
  
let rec string_of_prob p = 
  (* Everything is associative, but the normal form is sum of negated products.
   * So possbra below puts in _very_ visible brackets, for diagnostic purposes.
   *)
  let prio = function
    | P_0
    | P_1
    | P_f  
    | P_g 
    | P_h  _ 
    | Psymb _         -> 10
    | Pprod _         -> 8
    | Pneg  _         -> 6
    | Psum  _         -> 4
  in
  let possbra p' = 
    let supprio = prio p in
    let subprio = prio p' in
    let s = string_of_prob p' in
    if subprio<=supprio then "!!(" ^ s ^ ")!!" else s
  in
  match p with
  | P_0             -> "0"
  | P_1             -> "1"
  | P_f             -> "f"
  | P_g             -> "g"
  | P_h 1           -> "h"
  | P_h n           -> Printf.sprintf "h(%d)" n
  | Psymb (q,b,f)   -> Printf.sprintf "%s%s%s" (if b then "b" else "a") (string_of_int q) 
                                                (if !showabvalues then Printf.sprintf "[%f]" f else "")
  | Pneg p'         -> "-" ^ possbra p'
  | Pprod ps        -> String.concat "*" (List.map possbra ps)
  | Psum  ps        -> sum_separate (List.map possbra ps)    

and sum_separate = function
 | p1::p2::ps -> if Stringutils.starts_with p2 "-" then p1 ^ sum_separate (p2::ps) 
                 else p1 ^ "+" ^ sum_separate (p2::ps) 
 | [p]        -> p
 | []         -> raise (Can'tHappen "sum_separate []")

and string_of_cprob (C (x,y)) =
  let im y = 
    match y with
    | P_1     -> "i"
    | P_f  
    | P_g 
    | P_h   _ 
    | Psymb _ 
    | Pprod _ -> "i*" ^ string_of_prob y
    | _       -> "i*(" ^ string_of_prob y ^ ")"
  in
  match x,y with
  | P_0, P_0    -> "0"
  | _  , P_0    -> string_of_prob x
  | P_0, Pneg p -> "-" ^ im p
  | P_0, _      -> im y
  | _  , Pneg p -> "(" ^ string_of_prob x ^ "-" ^ im p ^ ")"
  | _  , _      -> "(" ^ string_of_prob x ^ "+" ^ im y ^ ")"
  
and string_of_qbit i = "#" ^ string_of_int i

and short_string_of_qbit i = string_of_qbit i

(* *********************** simplification ************************************ *)

(* The normal form is a sum of possibly-negated products. 
 * Both sums and products are left-recursive.
 * Products are sorted according to the type definition: i.e.
 * P_0, P_1, P_f, P_g, P_h, Psymb. But ... this isn't good enough. 
 
 * We need to sort identifiers according to their suffix: a0,b0,a1,b1, ...
 
 * Stdlib.compare works if we change the definition of Psymb, so I did
 
 *)

(* let compare p1 p2 =
     match p1, p2 with
     | Psymb (b1,q1,_), Psymb (b2,q2,_) -> Stdlib.compare (q1,b1) (q2,b2)
     | _                                -> Stdlib.compare p1      p2
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
          | Pprod p1s       , _                 -> simplify_prod (p2::p1s)
          | _                                   -> simplify_prod [p1;p2]
  in
  if !verbose_simplify then
    Printf.printf "rprod (%s) (%s) -> %s\n" (string_of_prob p1) (string_of_prob p2) (string_of_prob r);
  r

and make_prod = function
  | [p] -> p
  | []  -> P_1
  | ps  -> Pprod ps
  
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
            | P_g   :: P_h i :: ps    (* prefer f to g: gh^3 is gfg = fg^2 = f(h^2-h^3) so gh = f(1-h) *)
              when i>=1            -> premult (Psum [P_1; Pneg (P_h 1)]) (P_f :: (ihs (i-1) ps))
            | P_h i :: P_h j :: ps -> sp (ihs (i+j) r) ps
            | p              :: ps -> sp (p::r) ps
            | []                   -> None, List.rev r
          in
          let popt, ps = sp [] (sort Stdlib.compare ps) in
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
          | Psum p1s, _         -> simplify_sum (p2 :: p1s)
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
         (* | Pprod p1s, Pprod p2s -> Stdlib.compare p1s p2s *)
            | _                    -> Stdlib.compare p1 p2
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
            Listutils.null post
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
            | Pneg p1 :: p2      :: ps when p1=p2 -> sp again r ps
            | p1      :: Pneg p2 :: ps when p1=p2 -> sp again r ps
            (* the next lot are because h^j-h^(j+2) = h^j(1-h^2) = h^(j+2) 
               If it all works then we should allow also for j=0, and the whole mess
               prefixed with f (but not g, because of simplify_prod).
             *)
            | P_1        ::  ps  
                    when List.exists ((=) (Pneg (P_h 2))) ps
                                                  -> sp true (P_h 2::r) (Listutils.remove (Pneg (P_h 2)) ps)
            | Pneg (P_1) :: ps  
                    when List.exists ((=) (P_h 2)) ps  
                                                  -> sp true (Pneg (P_h 2)::r) (Listutils.remove (P_h 2) ps)
            | P_h j      ::  ps  
                    when List.exists ((=) (Pneg (P_h (j+2)))) ps
                                                  -> sp true (P_h (j+2)::r) (Listutils.remove (Pneg (P_h (j+2))) ps)
            | Pneg (P_h j) :: ps  
                    when List.exists ((=) (P_h (j+2))) ps  
                                                  -> sp true (Pneg (P_h (j+2))::r) (Listutils.remove (P_h (j+2)) ps)
            | Pprod (P_h j :: p1s) :: ps
                    when List.exists ((=) (Pneg (Pprod (P_h (j+2) :: p1s)))) ps                 
                                                  -> sp true (Pprod (P_h (j+2) :: p1s)::r) 
                                                             (Listutils.remove (Pneg (Pprod (P_h (j+2) :: p1s))) ps)
            | Pneg (Pprod (P_h j :: p1s)) :: ps
                    when List.exists ((=) (Pprod (P_h (j+2) :: p1s))) ps                 
                                                  -> sp true (Pneg (Pprod (P_h (j+2) :: p1s)) :: r) 
                                                             (Listutils.remove (Pprod (P_h (j+2) :: p1s)) ps)
            | (Pprod (P_h 2 :: p1s) as p1) :: ps  
                   when List.exists ((=) (Pneg (make_prod p1s))) ps 
                                                  -> sp true (Pneg p1::r) (Listutils.remove (Pneg (make_prod p1s)) ps)
            | (Pneg (Pprod (P_h 2 :: p1s) as p1)) :: ps  
                   when List.exists ((=) (make_prod p1s)) ps  
                                                  -> sp true (p1::r) (Listutils.remove (make_prod p1s) ps)
            | Pprod (P_f :: P_h 1 :: p1s) ::
              Pprod (P_f :: P_h 1 :: p2s) :: ps
                   when p1s=p2s && 
                        List.exists ((=) (Pneg (make_prod (P_f :: p1s)))) ps
                                                  -> sp true (make_prod (P_g :: p1s) :: r) 
                                                             (Listutils.remove (Pneg (make_prod (P_f :: p1s))) ps)
            | Pneg (Pprod (P_f :: P_h 1 :: p1s)) ::
              Pneg (Pprod (P_f :: P_h 1 :: p2s)) :: ps
                   when p1s=p2s && 
                        List.exists ((=) (make_prod (P_f :: p1s))) ps
                                                  -> sp true (Pneg (make_prod (P_g :: p1s)) :: r) 
                                                             (Listutils.remove (make_prod (P_f :: p1s)) ps)
            | p1      :: p2      :: ps when p1=p2 -> (match double p1 (p2::ps) with
                                                      | Some (p,ps) -> sp true (p::r) ps
                                                      | None        -> sp again (p1::r) (p2::ps)
                                                     )
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
          | ps  -> Psum (sort scompare ps)
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
(* in the case of dividing sums, look for factors fP-fhP, which is gh *)
and rdiv_sum_h orig_ps =
  let default () = sflatten (List.map rdiv_h orig_ps) (* sflatten because we can get a sum ... *) in
  let rec has_hfactor = function 
                         | Pneg p                               -> has_hfactor p
                         | P_h i                      
                         | Pprod (P_h i :: _)         
                         | Pprod (P_f :: P_h i :: _)  when i>=1 -> true
                         | _                                    -> false
  in
  let rec findit ps =
    match ps with
    | []                                     -> None
    | Pprod (P_f :: P_h _ :: _)        :: ps -> findit ps
    | Pprod (P_f :: ps')               :: ps -> if List.exists ((=) (Pneg (Pprod (P_f :: P_h 1 :: ps')))) orig_ps
                                                then Some (true, ps')
                                                else findit ps
    | Pneg (Pprod (P_f :: P_h _ :: _)) :: ps -> findit ps
    | Pneg (Pprod (P_f :: ps') )       :: ps -> if List.exists ((=) (Pprod (P_f :: P_h 1 :: ps'))) orig_ps
                                                then Some (false, ps')
                                                else findit ps
    | _                                :: ps -> findit ps
  in
  if List.for_all has_hfactor orig_ps then default ()
  else
  match findit orig_ps with
  | Some (true, ps)  -> Printf.printf "found %s and %s in rdiv_sum_h of %s\n"
                                      (string_of_prob (Pprod (P_f :: ps)))
                                      (string_of_prob (Pneg (Pprod (P_f :: P_h 1 :: ps))))
                                      (string_of_prob (Psum orig_ps));
                        default()
  | Some (false, ps) -> Printf.printf "found %s and %s in rdiv_sum_h of %s\n"
                                      (string_of_prob (Pneg (Pprod (P_f :: ps))))
                                      (string_of_prob (Pprod (P_f :: P_h 1 :: ps)))
                                      (string_of_prob (Psum orig_ps));
                        default()
  | None             -> default()
  
(* we can't really divide
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
 *)

(******** prob arithmetic is where all the action is. So we memoise sum and prod, carefully *********)

module ProbH = struct type t = prob 
                      let equal = (=)
                      let hash = Hashtbl.hash
                      let to_string = string_of_prob
               end
module ProbHash = MyHash.Make (ProbH)

let memofunProb f s = 
  let table = ProbHash.create 100 in
  ProbHash.memofun table (fun p -> if !verbose || !verbose_qcalc 
                                                     then Printf.printf "%s (%s)\n" s (string_of_prob p); 
                                                   f p
                                         )

let memofun2Prob f s = 
  let t1 = ProbHash.create 100 in
  ProbHash.memofun t1 
    (fun p1 -> let t2 = ProbHash.create 100 in
               ProbHash.memofun t2 
                 (fun p2 -> let r = f p1 p2 in
                            if !verbose || !verbose_qcalc 
                            then Printf.printf "%s (%s) (%s) -> %s\n" 
                                               s 
                                               (string_of_prob p1) 
                                               (string_of_prob p2)
                                               (string_of_prob r); 
                            r
                 )
    )

let raw_rprod = rprod
let memo_rprod = memofun2Prob rprod "rprod"

let rec rprod p1 p2 =
  if !Settings.memoise then
    match p1, p2 with
    (* we do 0, 1 and neg ourselves *)
    | P_0     , _
    | _       , P_0     -> P_0
    | P_1     , _       -> p2
    | _       , P_1     -> p1
    | Pneg  p1, _       -> rneg (rprod p1 p2)
    | _       , Pneg p2 -> rneg (rprod p1 p2)
    (* we memoise everything else *)
    | _                 -> memo_rprod p1 p2
  else
    raw_rprod p1 p2

let raw_rsum = rsum
let memo_rsum = memofun2Prob rsum "rsum"

let rec rsum p1 p2 =
  if !Settings.memoise then
    match p1, p2 with
    (* we do 0 ourselves *)
    | P_0     , _       -> p2
    | _       , P_0     -> p1
    (* we memoise sum *)
    | Psum  _ , _
    | _       , Psum  _ -> memo_rsum p1 p2
    (* everything else is raw *)
    | _                 -> raw_rsum p1 p2
  else
    raw_rsum p1 p2
  
(* *********************** complex arith in terms of reals ************************************ *)

let c_of_p p = C (p, P_0)

let c_0 = c_of_p P_0
let c_1 = c_of_p P_1
let c_h = c_of_p (P_h 1)
let c_f = c_of_p P_f
let c_g = c_of_p P_g

let c_i = C (P_0, P_1)

let cneg  (C (x,y)) = C (rneg x, rneg y)

let cprod (C (x1,y1) as c1) (C (x2,y2) as c2) = 
  match x1,y1, x2,y2 with
  | P_0     , P_0, _       , _    
  | _       , _  , P_0     , P_0       -> c_0
  | P_1     , P_0, _       , _         -> c2  
  | _       , _  , P_1     , P_0       -> c1
  | Pneg P_1, P_0, _       , _         -> cneg c2  
  | _       , _  , Pneg P_1, P_0       -> cneg c1
  | _       , P_0, _       , P_0       -> C (rprod x1 x2, P_0)            (* real    * real    *)
  | _       , P_0, _       , _         -> C (rprod x1 x2, rprod x1 y2)    (* real    * complex *)
  | _       , _  , _       , P_0       -> C (rprod x1 x2, rprod y1 x2)    (* complex * real    *)
  | _                                  -> C (rsum (rprod x1 x2) (rneg (rprod y1 y2)), rsum (rprod x1 y2) (rprod y1 x2))

let csum  (C (x1,y1) as c1) (C (x2,y2) as c2) = 
  match x1,y1, x2,y2 with
  | P_0, P_0, _  , _    -> c2 
  | _  , _  , P_0, P_0  -> c1
  | _                   -> C (rsum x1 x2, rsum y1 y2)

let cconj (C (x,y))               = C (x, rneg y)

let absq  (C (x,y))               = rsum (rprod x x) (rprod y y)

(* we can't really divide 
    let c_r_div   (C(x,y)) z          = C (rdiv x z, rdiv y z)
 *)
let c_r_div_h (C(x,y))            = C (rdiv_h x, rdiv_h y)

(* we no longer memoise any of these things ...

    module OrderedC = struct type t = cprob 
                             let compare = Stdlib.compare
                             let to_string = string_of_cprob
                      end
    module CMap = MyMap.Make (OrderedC)
    let memofunC f s = CMap.memofun id (fun c -> if !verbose || !verbose_qcalc then Printf.printf "%s (%s)\n" s (string_of_cprob c); f c)

    module OrderedC2 = struct type t = cprob*cprob 
                             let compare = Stdlib.compare
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
                             let compare = Stdlib.compare
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

    (* absq is used a lot in measurement: perhaps worth memoising. Or rather perhaps not,
       if rsum and rmult are memoised.
     *)
    let absq x = (if !Settings.memoise then memofunC absq "absq" else absq) x

    (* we can't really divide
        let c_r_div = memofunCP c_r_div "c_r_div"
     *)
    let c_r_div_h = memofunC c_r_div_h "c_r_div_h"
 *)
(* *********************** defining vectors, matrices ************************************ *)

let make_v ps = P_1, Array.of_list ps

let pcneg  (C (x,y)) = (* only for local use, please *)
  let negate = function
    | P_0 -> P_0
    | p   -> Pneg p
  in
  C (negate x, negate y) 

let v_zero  = make_v [c_1   ; c_0         ]
let v_one   = make_v [c_0   ; c_1         ]
let v_plus  = make_v [c_h   ; c_h         ]
let v_minus = make_v [c_h   ; pcneg c_h   ]

let v_1 = make_v [c_1] (* a unit for folding *)
let v_0 = make_v [c_0] (* another unit for folding *)

let string_of_cpaa m = 
  let strings_of_row r = Array.fold_right (fun p ss -> string_of_cprob p::ss) r [] in
  let block = Array.fold_right (fun r ss -> strings_of_row r::ss) m [] in
  let rwidth r = List.fold_left max 0 (List.map String.length r) in
  let width = List.fold_left max 0 (List.map rwidth block) in
  let pad s = s ^ String.make (width - String.length s) ' ' in
  let block = String.concat "\n "(List.map (String.concat " " <.> List.map pad) block) in
  Printf.sprintf "\n{%s}\n" block
  
let string_of_cpad v =
  Printf.sprintf "diag{" ^ string_of_list string_of_cprob " " (Array.to_list v) ^ "}"
  
let make_cpaa rows = rows |> (List.map Array.of_list) |> (Array.of_list)
let cpaa_of_gate = function
  | MGate m -> m
  | DGate v -> let n = vsize v in
               let zs = Listutils.tabulate n (const c_0) in
               let rows = Listutils.tabulate n (const zs) in
               let m = make_cpaa rows in
               for i = 0 to n-1 do
                 m.(i).(i) <- v.(i)
               done;
               m
               
let gate_of_cpaa m =
  let n = vsize m in
  let isdiag = _for_all 0 1 n (fun i ->
                               let row = m.(i) in
                               _for_all 0 1 n (fun j -> i=j || row.(j)=c_0)
                              )
  in
  if isdiag then
    DGate (Array.init n (fun i -> m.(i).(i)))
  else MGate m
  
let make_g rows = 
  gate_of_cpaa (make_cpaa rows)

let g_I  = make_g   [[c_1       ; c_0        ];
                     [c_0       ; c_1        ]] 
let g_X  = make_g   [[c_0       ; c_1        ];
                     [c_1       ; c_0        ]] 
let g_Y  = make_g   [[c_0       ; pcneg c_i  ];
                     [c_i       ; c_0        ]]
let g_Z  = make_g   [[c_1       ; c_0        ];
                     [c_0       ; pcneg c_1  ]] 
let g_H  = make_g   [[c_h       ; c_h        ];
                     [c_h       ; pcneg (c_h)]]
                     
(* these two are intended to be like rotations. Unlike H, Rz*Rz<>I *)

let g_Rz = make_g   [[c_f       ; pcneg c_g  ];
                     [c_g       ; c_f        ]]
let g_G  = make_g   [[c_g       ; pcneg c_f  ];
                     [c_f       ; c_g        ]]

(* experimental Rx(pi/8) gate *)

let g_Rx = make_g   [[c_1       ; c_0        ];
                     [c_0       ; C(P_f,P_g) ]]
                     
let g_Phi = function (* as Pauli *)
  | 0 -> g_I
  | 1 -> g_X
  | 2 -> g_Y  
  | 3 -> g_Z  
  | i -> raise (Disaster ("** _Phi(" ^ string_of_int i ^ ")"))

let g_Swap =
  make_g [[c_1; c_0; c_0; c_0];
          [c_0; c_0; c_1; c_0];
          [c_0; c_1; c_0; c_0];
          [c_0; c_0; c_0; c_1]]
          
let g_Toffoli = (* tediously, sorry *)
  make_g  [[c_1; c_0; c_0; c_0; c_0; c_0; c_0; c_0 ];
           [c_0; c_1; c_0; c_0; c_0; c_0; c_0; c_0 ];
           [c_0; c_0; c_1; c_0; c_0; c_0; c_0; c_0 ];
           [c_0; c_0; c_0; c_1; c_0; c_0; c_0; c_0 ];
           [c_0; c_0; c_0; c_0; c_1; c_0; c_0; c_0 ];
           [c_0; c_0; c_0; c_0; c_0; c_1; c_0; c_0 ];
           [c_0; c_0; c_0; c_0; c_0; c_0; c_0; c_1 ];
           [c_0; c_0; c_0; c_0; c_0; c_0; c_1; c_0 ]]
           
let g_Fredkin = (* tediously, sorry *)
  make_g  [[c_1; c_0; c_0; c_0; c_0; c_0; c_0; c_0 ];
           [c_0; c_1; c_0; c_0; c_0; c_0; c_0; c_0 ];
           [c_0; c_0; c_1; c_0; c_0; c_0; c_0; c_0 ];
           [c_0; c_0; c_0; c_1; c_0; c_0; c_0; c_0 ];
           [c_0; c_0; c_0; c_0; c_1; c_0; c_0; c_0 ];
           [c_0; c_0; c_0; c_0; c_0; c_0; c_1; c_0 ];
           [c_0; c_0; c_0; c_0; c_0; c_1; c_0; c_0 ];
           [c_0; c_0; c_0; c_0; c_0; c_0; c_0; c_1 ]]
           
let make_C g = 
  let m = cpaa_of_gate g in
  make_g  [[c_1; c_0; c_0      ; c_0       ];
           [c_0; c_1; c_0      ; c_0       ];
           [c_0; c_0; m.(0).(0); m.(0).(1) ];
           [c_0; c_0; m.(1).(0); m.(1).(1) ]]
    
let g_CX   = make_C g_X
let g_CY   = make_C g_Y
let g_CZ   = make_C g_Z 
let g_Cnot = g_CX
                      
let g_1 = make_g [[c_1]] (* a unit for folding *)
let g_0 = make_g [[c_0]] (* another unit for folding, maybe *)

(* the special Grover gate. Oh this is a filthy hack. *)
let groverG n =
  if n<1 || n>=20 then raise (Error (Printf.sprintf "grovergate %d" n)) else
  (let p = P_h (2*(n-1)) in
   let cp = c_of_p p in
   let size = 1 lsl n in
   let row _ = Array.init size (fun _ -> cp) in
   let m = Array.init size row in
   let p' = csum (cneg c_1) cp in
   for i=0 to size-1 do
     m.(i).(i) <- p'
   done;
   gate_of_cpaa m
  )
  
let groverU bs =
  let ns = List.map (fun b -> if b then 1 else 0) bs in
  let size = 1 lsl (List.length ns) in
  let rec address r ns =
    match ns with
    | n::ns -> address (2*r+n) ns
    | []    -> r
  in
  let k = address 0 ns in
  let row i = Array.init size (fun j -> if i=j then
                                          (if j=k then cneg c_1 else c_1)
                                        else c_0
                              ) 
  in
  let m = Array.init size row in
  gate_of_cpaa m
  

(* string_of_ functions *)
let string_of_pqueue stringof sep pq = 
  "{" ^ string_of_list stringof sep (PQueue.elements pq) ^ "}"
;;

(* so_value takes an argument optf to winnow out those things we don't want it to deal with directly *)
(* this is to allow the library function 'show' to work properly. The rest of the world can use string_of_value *)
let rec so_value optf v =
  match optf v with
  | Some s -> s
  | None   -> (match v with
               | VUnit           -> "()"
               | VBit b          -> if b then "1" else "0"
               | VNum n          -> string_of_num n
               | VBool b         -> string_of_bool b
               | VBra b          -> string_of_bra b
               | VKet k          -> string_of_ket k
               | VGate gate      -> string_of_gate gate
               | VChar c         -> Printf.sprintf "'%s'" (Char.escaped c)
               | VString s       -> Printf.sprintf "\"%s\"" (String.escaped s)
               | VQbit q         -> "Qbit " ^ string_of_qbit q
               | VQstate s       -> s
               | VChan c         -> "Chan " ^ so_chan optf c
               | VTuple vs       -> "(" ^ string_of_list (so_value optf) "," vs ^ ")"
               | VList vs        -> bracketed_string_of_list (so_value optf) vs
               | VFun f          -> "<function>"
               | VProcess (n,_,ns,p) (* don't print the env: it will be an infinite recursion *)
                                 -> Printf.sprintf "process %s .. (%s) %s"
                                                      (string_of_name n)
                                                      (string_of_list string_of_name "," ns)
                                                      (string_of_process p)
              )

and short_so_value optf v =
  match optf v with
  | Some s -> s
  | None   -> (match v with
               | VQbit q         -> "Qbit " ^ short_string_of_qbit q
               | VChan c         -> "Chan " ^ short_so_chan optf c ^ if c.traced then "" else "(untraced)"
               | VTuple vs       -> "(" ^ string_of_list (short_so_value optf) "," vs ^ ")"
               | VList vs        -> bracketed_string_of_list (short_so_value optf) vs
               | VProcess (n,_,ns,_) 
                                 -> Printf.sprintf "process %s .. (%s)"
                                                      (string_of_name n)
                                                      (string_of_list string_of_name "," ns)
               | v               -> so_value optf v
              )
  
and so_chan optf {cname=i; traced=traced; stream=vs; rwaiters=rq; wwaiters=wq} =
    Printf.sprintf "%d%s = vs:{%s} rs:{%s} ws:{%s}"
                   i
                   (if traced then "" else "(untraced)")
                   (string_of_queue (so_value optf) "; " vs)
                   (string_of_pqueue (short_so_rwaiter optf) "; " rq)
                   (string_of_pqueue (short_so_wwaiter optf) "; " wq)

and short_so_chan optf {cname=i} =
    string_of_int i
    
and so_env optf env =
  "{" ^ string_of_monenv "=" (so_value optf) env ^ "}"

and short_so_env optf = so_env optf (* <.> (Monenv.filterg (function 
                                                        | _, VFun     _ 
                                                        | _, VProcess _ -> false
                                                        | _             -> true
                                                        )
                                         ) *)
  
and so_runner optf (n, proc, env) =
  Printf.sprintf "%s = (%s) %s" 
                 (string_of_name n)
                 (short_string_of_process proc)
                 (short_so_env optf env)
                 
and so_rwaiter optf ((n, pat, proc, env),gsir) = 
  Printf.sprintf "%s = (%s)%s %s%s" 
                 (string_of_name n)
                 (string_of_pattern pat)
                 (short_string_of_process proc)
                 (short_so_env optf env)
                 (if fst !gsir then "" else "[dead]")
                 
and short_so_rwaiter optf ((n, pat, proc, env),gsir) = (* infinite loop if we print the environment *)
  Printf.sprintf "%s(%s)%s" 
                 (string_of_name n)
                 (string_of_pattern pat)
                 (if fst !gsir then "" else "[dead]")
                 
and so_wwaiter optf ((n, v, proc, env),gsir) = 
  Printf.sprintf "%s = (%s)%s %s%s" 
                 (string_of_name n)
                 (so_value optf v)
                 (short_string_of_process proc)
                 (short_so_env optf env)
                 (if fst !gsir then "" else "[dead]")
                 
and short_so_wwaiter optf ((n, v, proc, env),gsir) = (* infinite loop if we print the environment *)
  Printf.sprintf "%s(%s)%s" 
                 (string_of_name n)
                 (so_value optf v)
                 (if fst !gsir then "" else "[dead]")
                 
and so_runnerqueue optf sep rq =
  string_of_pqueue (so_runner optf) sep rq

and so_pv v =
  if !Settings.fancyvec then 
    (let n = vsize v in
     let rec ln2 n r = if n=1 then r
                       else ln2 (n lsr 1) (r+1)
     in
     let width = ln2 n 0 in
     let string_of_bin i =
       let rec sb i k =
         if k=width then ""
         else sb (i/2) (k+1) ^ (if i mod 2 = 0 then "0" else "1")
       in
       sb i 0
     in
     let string_of_basis_idx i =
       Printf.sprintf "|%s>" (string_of_bin i)
     in
     let mustbracket (C(real,im)) = 
       (* all but simple real sums are bracketed in string_of_cprob *)
       match real, im with
       | Psum _, P_0 -> true
       | _           -> false
     in
     let estrings = _for_leftfold 0 1 n
                      (fun i ss -> match string_of_cprob v.(i) with
                                   | "0"  -> ss
                                   | "1"  -> (string_of_basis_idx i) :: ss
                                   | "-1" -> ("-" ^ string_of_basis_idx i) :: ss
                                   | s   ->  (Printf.sprintf "%s%s" 
                                                             (if mustbracket v.(i) then "(" ^s ^ ")" else s) 
                                                             (string_of_basis_idx i)
                                             ) :: ss
                      )
                      []
     in
     match estrings with
     | []  -> "??empty probvec??"
     | [e] -> e
     | _   -> Printf.sprintf "(%s)" (sum_separate (List.rev estrings))
    )
  else
    (let estrings = Array.fold_right (fun p ss -> string_of_cprob p::ss) v [] in
     Printf.sprintf "(%s)" (String.concat " <,> " estrings)
    )
  
and string_of_probvec = function
  | P_1, vv -> so_pv vv
  | vm , vv -> Printf.sprintf "<<%s>>%s" (string_of_prob vm) (so_pv vv)
  
and string_of_gate g = 
  let nameopt = if !Settings.showsymbolicgate then
                  (if g=g_I       then Some "I" else
                   if g=g_X       then Some "X" else
                   if g=g_Y       then Some "Y" else
                   if g=g_Z       then Some "Z" else
                   if g=g_H       then Some "H" else
                   if g=g_Rz      then Some "Rz" else
                   if g=g_Rx      then Some "Rx" else
                   if g=g_Cnot    then Some "Cnot" else
                   if g=g_Swap    then Some "Swap" else
                   if g=g_Toffoli then Some "T" else 
                   if g=g_Fredkin then Some "F" else 
                   None
                  )
                else None
  in
  match nameopt with 
  | Some s -> s
  | None   -> (match g with
               | MGate m -> string_of_cpaa m
               | DGate v -> string_of_cpad v
              )

(* ********************************************************************************************************** *)

let doptf s = None

let string_of_value = so_value doptf
let short_string_of_value = short_so_value doptf 

let string_of_env = so_env doptf
let short_string_of_env = short_so_env doptf 

let string_of_chan = so_chan doptf
let short_string_of_chan = short_so_chan doptf 

let string_of_runnerqueue = so_runnerqueue doptf

