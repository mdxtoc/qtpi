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
open Snum
open Forutils

exception Disaster of string
exception Error of string

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
  | VChar of Uchar.t
  | VBra of snv
  | VKet of snv
  | VMatrix of matrix
  | VGate of gate
  | VString of string
  | VQbit of qbit
  | VQstate of string
  | VChan of chan
  | VTuple of value list
  | VList of value list
  | VFun of (value -> value)        (* with the environment baked in for closures *)
  | VProcess of name * env ref * name list * process

and gate = 
    | MGate of csnum array array   (* square matrix *)
    | DGate of csnum array         (* diagonal matrix *)

and matrix = csnum array array     (* not necessarily square *)

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
  
let string_of_qbit i = "#" ^ string_of_int i

let short_string_of_qbit = string_of_qbit

(* *********************** simplification ************************************ *)

(* The normal form is a sum of possibly-negated products. 
 * Both sums and products are left-recursive.
 * Products are sorted according to the type definition: i.e.
 * S_0, S_1, S_f, S_g, S_h, S_symb. But ... this isn't good enough. 
 
 * We need to sort identifiers according to their suffix: a0,b0,a1,b1, ...
 
 * Stdlib.compare works if we change the definition of S_symb, so I did
 
 *)

(* let compare s1 s2 =
     match s1, s2 with
     | S_symb (b1,q1,_), S_symb (b2,q2,_) -> Stdlib.compare (q1,b1) (q2,b2)
     | _                                -> Stdlib.compare s1      s2
*)
(* we deal with long lists. Avoid sorting if poss *)
let sort compare ss =
  let rec check ss' =
    match ss' with
    | s'::(s''::_ as ss') -> if s'<s'' then check ss' else List.sort compare ss
    | _                   -> ss
  in
  check ss
  
let rec rneg s =
  let r = match s with
          | S_neg s        -> s
          | S_0           -> s
          | S_sum ss       -> simplify_sum (List.map rneg ss)
          | _             -> S_neg s
  in
  if !verbose_simplify then
    Printf.printf "rneg (%s) -> %s\n" (string_of_snum s) (string_of_snum r);
  r
    
and rprod s1 s2 =
  let r = match s1, s2 with
          | S_0             , _
          | _               , S_0               -> S_0
          | S_1             , _                 -> s2
          | _               , S_1               -> s1
          | S_neg s1         , _                 -> rneg (rprod s1 s2)
          | _               , S_neg s2           -> rneg (rprod s1 s2)
          | _               , S_sum s2s          -> let ss = List.map (rprod s1) s2s in
                                                   simplify_sum (sflatten ss)
          | S_sum s1s        , _                 -> let ss = List.map (rprod s2) s1s in
                                                   simplify_sum (sflatten ss)
          | S_prod s1s       , S_prod s2s         -> simplify_prod (s1s @ s2s)
          | _               , S_prod s2s         -> simplify_prod (s1 :: s2s)
          | S_prod s1s       , _                 -> simplify_prod (s2::s1s)
          | _                                   -> simplify_prod [s1;s2]
  in
  if !verbose_simplify then
    Printf.printf "rprod (%s) (%s) -> %s\n" (string_of_snum s1) (string_of_snum s2) (string_of_snum r);
  r

and make_prod = function
  | [s] -> s
  | []  -> S_1
  | ss  -> S_prod ss
  
(* warning: this can deliver a sum, which mucks up the normal form *)
and simplify_prod ss = (* We deal with constants, f^2, g^2, gh, fg *)
  let r = let rec sp r ss = 
            let premult s ss = 
              let popt, ss = sp r ss in
              (match popt with 
               | Some pre_p -> Some (rprod pre_p s)
               | None       -> Some s
              ), ss
            in
            match ss with
            | S_0            :: ss -> None, [S_0]
            | S_1            :: ss 
            | S_h 0          :: ss -> sp r ss
            | S_f   :: S_f   :: ss -> premult (S_sum [S_h 2; S_h 3]) ss
            | S_f   :: S_g   :: ss -> premult (S_h 3) ss
            | S_g   :: S_g   :: ss -> premult (S_sum [S_h 2; S_neg (S_h 3)]) ss
(*          | S_g   :: S_h i :: ss    (* prefer f to g: gh^3 is gfg = fg^2 *)
              when i>=3            -> sp (S_f :: r) (S_g :: S_g :: (ihs (i-3) ss)) 
 *)
            | S_g   :: S_h i :: ss    (* prefer f to g: gh^3 is gfg = fg^2 = f(h^2-h^3) so gh = f(1-h) *)
              when i>=1            -> premult (S_sum [S_1; S_neg (S_h 1)]) (S_f :: (ihs (i-1) ss))
            | S_h i :: S_h j :: ss -> sp (ihs (i+j) r) ss
            | s              :: ss -> sp (s::r) ss
            | []                   -> None, List.rev r
          in
          let popt, ss = sp [] (sort Stdlib.compare ss) in
          let s = match ss with 
                  | []  -> S_1
                  | [s] -> s 
                  | _   -> S_prod ss 
          in
          match popt with 
          | Some pre_p -> rprod pre_p s
          | None       -> s
  in
  if !verbose_simplify then
    Printf.printf "simplify_prod %s -> %s\n" (bracketed_string_of_list string_of_snum ss) (string_of_snum r);
  r

and rsum s1 s2 = 
  let r = match s1, s2 with
          | S_0     , _         -> s2
          | _       , S_0       -> s1
          | S_sum s1s, S_sum s2s  -> simplify_sum (s1s @ s2s)
          | _       , S_sum s2s  -> simplify_sum (s1 :: s2s)
          | S_sum s1s, _         -> simplify_sum (s2 :: s1s)
          | _                   -> simplify_sum [s1;s2]
  in
  if !verbose_simplify then
    Printf.printf "rsum (%s) (%s) -> %s\n" (string_of_snum s1) (string_of_snum s2) (string_of_snum r);
  r

and sflatten ss = (* flatten a list of sums *)
  let rec sf ss s = 
    match s with
    | S_sum ss' -> ss' @ ss
    | _        -> s :: ss
  in
  let r = if List.exists (function S_sum _ -> true | _ -> false) ss 
          then List.fold_left sf [] ss   
          else ss
  in
  if !verbose_simplify then
    Printf.printf "sflatten %s -> %s\n" 
                  (bracketed_string_of_list string_of_snum ss) 
                  (bracketed_string_of_list string_of_snum r);
  r

and ihs i ss = if i=0 then ss else S_h i::ss

and simplify_sum ss = 
  let r = let rec scompare s1 s2 = (* ignore negation *)
            match s1, s2 with
            | S_neg s1  , S_neg s2   -> scompare s1 s2
            | S_neg s1  , _         -> scompare s1 s2
            | _        , S_neg s2   -> scompare s1 s2
         (* | S_prod s1s, S_prod s2s -> Stdlib.compare s1s s2s *)
            | _                    -> Stdlib.compare s1 s2
          in
          let rec double s1 rest = (* looking for h^2k*X+h^2k*X+.... *)
            (* find the h entry, if any, in s1 *)
            let rec split3 isneg pres ss =
              match ss with 
              | S_h i :: ss -> if i>=2 then Some (isneg, pres, i, ss) else None
              | s     :: ss -> split3 isneg (s::pres) ss
              | []          -> None
            in
            let rec nsplit3 isneg = function
                                    | S_neg s          -> nsplit3 (not isneg) s
                                    | S_h i when i>=2 -> Some (isneg,[],i,[])
                                    | S_prod ss        -> split3 isneg [] ss
                                    | _               -> None
            in
            let r = match nsplit3 false s1 with
                    | Some (isneg,pres,maxi,posts) ->
                        (* i is how many hs we use up, k is 2^(i/2) *)
                        let rec gofor i k rest =
                          let rec takeeqs k rest =
                            match k, rest with
                            | 0, _       -> Some rest
                            | _, s::rest -> if s1=s then takeeqs (k-1) rest else None
                            | _, []      -> None
                          in
                          if i>maxi then None else
                          takeeqs k rest &~~ (fun rest -> gofor (i+2) (k*2) rest
                                                          |~~ (fun _ -> let r = Some ((if isneg then rneg else id)
                                                                                        (simplify_prod (prepend pres (S_h (maxi-i)::posts))),
                                                                                      rest
                                                                                     )
                                                                          in
                                                                          if !verbose_simplify then
                                                                            Printf.printf "gofor %d %d %s (s1=%s)-> %s\n"
                                                                                            i
                                                                                            k
                                                                                            (bracketed_string_of_list string_of_snum rest)
                                                                                            (string_of_snum s1)
                                                                                            (string_of_option (string_of_pair string_of_snum (bracketed_string_of_list string_of_snum) ",") r);
                                                                          r
                                                              )
                                             )
                        in
                        gofor 2 1 rest
                    | _                            -> None
            in
            if !verbose_simplify then
              Printf.printf "double (%s) %s -> %s\n" (string_of_snum s1)  
                                                     (bracketed_string_of_list string_of_snum rest)
                                                     (string_of_option (string_of_pair string_of_snum (bracketed_string_of_list string_of_snum) ",") r);
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
          let rec a2b2 s1 s2 = (* looking for X*a^2+X*b^2 *)
            let r = match s1, s2 with
                    | S_neg s1         , S_neg s2             -> a2b2 s1 s2 &~~ (_Some <.> rneg)
                    | S_prod s1s       , S_prod s2s           ->
                        (try let pps = zip s1s s2s in
                             let pre, rest = partition_1 pps in
                             match rest with
                             | (S_symb (q1, false, _), S_symb (q2, true, _)) ::
                               (S_symb (q3, false, _), S_symb (q4, true, _)) :: post  
                               when q1=q2 && q1=q3 && q1=q4 && all_same post
                                     -> takeit pre post
                             | _     -> None
                         with Zip -> None
                        )
                    | _                                     -> None
            in
            if !verbose_simplify then
              Printf.printf "a2b2 (%s) (%s) -> %s\n" (string_of_snum s1)  
                                                     (string_of_snum s2)
                                                     (string_of_option string_of_snum r);
            r
          in
          let rec sp again r ss =
            match ss with
            | S_0                :: ss            -> sp again r ss
            | S_neg s1 :: s2      :: ss when s1=s2 -> sp again r ss
            | s1      :: S_neg s2 :: ss when s1=s2 -> sp again r ss
            (* the next lot are because h^j-h^(j+2) = h^j(1-h^2) = h^(j+2) 
               If it all works then we should allow also for j=0, and the whole mess
               prefixed with f (but not g, because of simplify_prod).
             *)
            | S_1        ::  ss  
                    when List.exists ((=) (S_neg (S_h 2))) ss
                                                  -> sp true (S_h 2::r) (Listutils.remove (S_neg (S_h 2)) ss)
            | S_neg (S_1) :: ss  
                    when List.exists ((=) (S_h 2)) ss  
                                                  -> sp true (S_neg (S_h 2)::r) (Listutils.remove (S_h 2) ss)
            | S_h j      ::  ss  
                    when List.exists ((=) (S_neg (S_h (j+2)))) ss
                                                  -> sp true (S_h (j+2)::r) (Listutils.remove (S_neg (S_h (j+2))) ss)
            | S_neg (S_h j) :: ss  
                    when List.exists ((=) (S_h (j+2))) ss  
                                                  -> sp true (S_neg (S_h (j+2))::r) (Listutils.remove (S_h (j+2)) ss)
            | S_prod (S_h j :: s1s) :: ss
                    when List.exists ((=) (S_neg (S_prod (S_h (j+2) :: s1s)))) ss                 
                                                  -> sp true (S_prod (S_h (j+2) :: s1s)::r) 
                                                             (Listutils.remove (S_neg (S_prod (S_h (j+2) :: s1s))) ss)
            | S_neg (S_prod (S_h j :: s1s)) :: ss
                    when List.exists ((=) (S_prod (S_h (j+2) :: s1s))) ss                 
                                                  -> sp true (S_neg (S_prod (S_h (j+2) :: s1s)) :: r) 
                                                             (Listutils.remove (S_prod (S_h (j+2) :: s1s)) ss)
            | (S_prod (S_h 2 :: s1s) as s1) :: ss  
                   when List.exists ((=) (S_neg (make_prod s1s))) ss 
                                                  -> sp true (S_neg s1::r) (Listutils.remove (S_neg (make_prod s1s)) ss)
            | (S_neg (S_prod (S_h 2 :: s1s) as s1)) :: ss  
                   when List.exists ((=) (make_prod s1s)) ss  
                                                  -> sp true (s1::r) (Listutils.remove (make_prod s1s) ss)
            | S_prod (S_f :: S_h 1 :: s1s) ::
              S_prod (S_f :: S_h 1 :: s2s) :: ss
                   when s1s=s2s && 
                        List.exists ((=) (S_neg (make_prod (S_f :: s1s)))) ss
                                                  -> sp true (make_prod (S_g :: s1s) :: r) 
                                                             (Listutils.remove (S_neg (make_prod (S_f :: s1s))) ss)
            | S_neg (S_prod (S_f :: S_h 1 :: s1s)) ::
              S_neg (S_prod (S_f :: S_h 1 :: s2s)) :: ss
                   when s1s=s2s && 
                        List.exists ((=) (make_prod (S_f :: s1s))) ss
                                                  -> sp true (S_neg (make_prod (S_g :: s1s)) :: r) 
                                                             (Listutils.remove (make_prod (S_f :: s1s)) ss)
            | s1      :: s2      :: ss when s1=s2 -> (match double s1 (s2::ss) with
                                                      | Some (s,ss) -> sp true (s::r) ss
                                                      | None        -> sp again (s1::r) (s2::ss)
                                                     )
            | s1      :: s2      :: ss            -> (match a2b2 s1 s2 with
                                                      | Some s -> sp true (s::r) ss
                                                      | None   -> sp again (s1::r) (s2::ss)
                                                     )
            | s                  :: ss            -> sp again (s::r) ss
            | []                                  -> let r = List.rev r in
                                                    if again then doit (sflatten r) else r
          and doit ss = sp false [] (sort scompare ss)
          in
          if List.exists (function S_sum _ -> true | S_neg (S_sum _) -> true | _ -> false) ss then
            raise (Error (Printf.sprintf "simplify_sum (%s)" (string_of_snum (S_sum ss))))
          else
          match doit ss with
          | []  -> S_0
          | [s] -> s
          | ss  -> S_sum (sort scompare ss)
  in
  if !verbose_simplify then
    Printf.printf "simplify_sum (%s) -> %s\n" (string_of_snum (S_sum ss)) (string_of_snum r);
  r

and sqrt_half i =   (* (1/sqrt 2)**i *)
  let r = if i=0 then S_1 else S_h i in
  if !verbose_simplify then
    Printf.printf "sqrt_half %d -> %s\n" i (string_of_snum r);
  r

(* warning: this can deliver a sum *)
and rdiv_h s = (* multiply by sqrt 2 (= divide by h). Happens: see normalise *)
  let r = match s with
          | S_0                              -> s
          | S_neg s                           -> rneg (rdiv_h s)
          | S_h i                  when i>=1 -> sqrt_half (i-1)
          | S_prod (     S_h i::ss) when i>=1 -> simplify_prod (     sqrt_half (i-1) :: ss)
          | S_prod (S_f::S_h i::ss) when i>=1 -> simplify_prod (S_f::sqrt_half (i-1) :: ss)
          | S_prod (S_g::S_h i::ss) when i>=1 -> simplify_prod (S_g::sqrt_half (i-1) :: ss)
          | S_sum  ss                         -> simplify_sum  (sflatten (List.map rdiv_h ss)) (* sflatten because we can get a sum ... *)
          | _                                -> (* s/h = (sh^2+sh^2)/h = sh+sh *)
                                                let ph = rprod s (S_h 1) in
                                                rsum ph ph
  in
  if !verbose_simplify then
    Printf.printf "rdiv_h (%s) -> %s\n" (string_of_snum s) (string_of_snum r);
  r
(* in the case of dividing sums, look for factors fP-fhP, which is gh *)
and rdiv_sum_h orig_ps =
  let default () = sflatten (List.map rdiv_h orig_ps) (* sflatten because we can get a sum ... *) in
  let rec has_hfactor = function 
                         | S_neg s                               -> has_hfactor s
                         | S_h i                      
                         | S_prod (S_h i :: _)         
                         | S_prod (S_f :: S_h i :: _)  when i>=1 -> true
                         | _                                    -> false
  in
  let rec findit ss =
    match ss with
    | []                                     -> None
    | S_prod (S_f :: S_h _ :: _)        :: ss -> findit ss
    | S_prod (S_f :: ss')               :: ss -> if List.exists ((=) (S_neg (S_prod (S_f :: S_h 1 :: ss')))) orig_ps
                                                then Some (true, ss')
                                                else findit ss
    | S_neg (S_prod (S_f :: S_h _ :: _)) :: ss -> findit ss
    | S_neg (S_prod (S_f :: ss') )       :: ss -> if List.exists ((=) (S_prod (S_f :: S_h 1 :: ss'))) orig_ps
                                                then Some (false, ss')
                                                else findit ss
    | _                                :: ss -> findit ss
  in
  if List.for_all has_hfactor orig_ps then default ()
  else
  match findit orig_ps with
  | Some (true, ss)  -> Printf.printf "found %s and %s in rdiv_sum_h of %s\n"
                                      (string_of_snum (S_prod (S_f :: ss)))
                                      (string_of_snum (S_neg (S_prod (S_f :: S_h 1 :: ss))))
                                      (string_of_snum (S_sum orig_ps));
                        default()
  | Some (false, ss) -> Printf.printf "found %s and %s in rdiv_sum_h of %s\n"
                                      (string_of_snum (S_neg (S_prod (S_f :: ss))))
                                      (string_of_snum (S_prod (S_f :: S_h 1 :: ss)))
                                      (string_of_snum (S_sum orig_ps));
                        default()
  | None             -> default()
  
(* we can't really divide
    and rdiv s1 s2 = (* happens in normalise *) (* this needs work for division by sums and also for division by products *)
      let bad () = 
        raise (Error (Printf.sprintf "rdiv (%s) (%s)" (string_of_snum s1) (string_of_snum s2)))
      in
      let r = match s1 with
              | S_0               -> S_0
              | _ when s1=s2      -> S_1
              | S_neg s1           -> rneg (rdiv s1 s2)
              | S_prod ss          -> let rec del ss =
                                       match ss with
                                       | [] -> bad()
                                       | s::ss -> if s=s2 then ss else s::del ss
                                     in
                                     S_prod (del ss)
              | S_sum ss           -> simplify_sum (List.map (fun s -> rdiv s s2) ss)
              | _                 -> bad ()
      in
      if !verbose_simplify then
        Printf.printf "rdiv (%s) (%s) -> %s\n" (string_of_snum s1) (string_of_snum s2) (string_of_snum r);
      r
 *)

(******** snum arithmetic is where all the action is. So we memoise sum and prod, carefully *********)

module ProbH = struct type t = snum 
                      let equal = (=)
                      let hash = Hashtbl.hash
                      let to_string = string_of_snum
               end
module ProbHash = MyHash.Make (ProbH)

let memofunProb f str = 
  let table = ProbHash.create 100 in
  ProbHash.memofun table (fun s -> if !verbose || !verbose_qcalc 
                                                     then Printf.printf "%s (%s)\n" str (string_of_snum s); 
                                                   f s
                                         )

let memofun2Prob f str = 
  let t1 = ProbHash.create 100 in
  ProbHash.memofun t1 
    (fun s1 -> let t2 = ProbHash.create 100 in
               ProbHash.memofun t2 
                 (fun s2 -> let r = f s1 s2 in
                            if !verbose || !verbose_qcalc 
                            then Printf.printf "%s (%s) (%s) -> %s\n" 
                                               str 
                                               (string_of_snum s1) 
                                               (string_of_snum s2)
                                               (string_of_snum r); 
                            r
                 )
    )

let raw_rprod = rprod
let memo_rprod = memofun2Prob rprod "rprod"

let rec rprod s1 s2 =
  if !Settings.memoise then
    match s1, s2 with
    (* we do 0, 1 and neg ourselves *)
    | S_0     , _
    | _       , S_0     -> S_0
    | S_1     , _       -> s2
    | _       , S_1     -> s1
    | S_neg  s1, _       -> rneg (rprod s1 s2)
    | _       , S_neg s2 -> rneg (rprod s1 s2)
    (* we memoise everything else *)
    | _                 -> memo_rprod s1 s2
  else
    raw_rprod s1 s2

let raw_rsum = rsum
let memo_rsum = memofun2Prob rsum "rsum"

let rec rsum s1 s2 =
  if !Settings.memoise then
    match s1, s2 with
    (* we do 0 ourselves *)
    | S_0     , _       -> s2
    | _       , S_0     -> s1
    (* we memoise sum *)
    | S_sum  _ , _
    | _       , S_sum  _ -> memo_rsum s1 s2
    (* everything else is raw *)
    | _                 -> raw_rsum s1 s2
  else
    raw_rsum s1 s2
  
(* *********************** complex arith in terms of reals ************************************ *)

let c_of_p s = C (s, S_0)

let c_0 = c_of_p S_0
let c_1 = c_of_p S_1
let c_h = c_of_p (S_h 1)
let c_f = c_of_p S_f
let c_g = c_of_p S_g

let c_i = C (S_0, S_1)

let cneg  (C (x,y)) = C (rneg x, rneg y)

let cprod (C (x1,y1) as c1) (C (x2,y2) as c2) = 
  match x1,y1, x2,y2 with
  | S_0     , S_0, _       , _    
  | _       , _  , S_0     , S_0       -> c_0
  | S_1     , S_0, _       , _         -> c2  
  | _       , _  , S_1     , S_0       -> c1
  | S_neg S_1, S_0, _       , _         -> cneg c2  
  | _       , _  , S_neg S_1, S_0       -> cneg c1
  | _       , S_0, _       , S_0       -> C (rprod x1 x2, S_0)            (* real    * real    *)
  | _       , S_0, _       , _         -> C (rprod x1 x2, rprod x1 y2)    (* real    * complex *)
  | _       , _  , _       , S_0       -> C (rprod x1 x2, rprod y1 x2)    (* complex * real    *)
  | _                                  -> C (rsum (rprod x1 x2) (rneg (rprod y1 y2)), rsum (rprod x1 y2) (rprod y1 x2))

let csum  (C (x1,y1) as c1) (C (x2,y2) as c2) = 
  match x1,y1, x2,y2 with
  | S_0, S_0, _  , _    -> c2 
  | _  , _  , S_0, S_0  -> c1
  | _                   -> C (rsum x1 x2, rsum y1 y2)

let cdiff c1 c2 = csum c1 (cneg c2)

let cconj (C (x,y))               = C (x, rneg y)

let absq  (C (x,y))               = rsum (rprod x x) (rprod y y)

(* we can't really divide 
    let c_r_div   (C(x,y)) z          = C (rdiv x z, rdiv y z)
 *)
let c_r_div_h (C(x,y))            = C (rdiv_h x, rdiv_h y)

(* we no longer memoise any of these things ...

    module OrderedC = struct type t = csnum 
                             let compare = Stdlib.compare
                             let to_string = string_of_csnum
                      end
    module CMap = MyMap.Make (OrderedC)
    let memofunC f s = CMap.memofun id (fun c -> if !verbose || !verbose_qcalc then Printf.printf "%s (%s)\n" s (string_of_csnum c); f c)

    module OrderedC2 = struct type t = csnum*csnum 
                             let compare = Stdlib.compare
                             let to_string = bracketed_string_of_pair string_of_csnum string_of_csnum
                      end
    module C2Map = MyMap.Make (OrderedC2)
    let memofunC2 f s = 
      curry2 (C2Map.memofun id (uncurry2 (fun c1 c2 -> if !verbose || !verbose_qcalc then 
                                                         Printf.printf "%s (%s) (%s)\n" 
                                                                       s (string_of_csnum c1) (string_of_csnum c2);
                                                       f c1 c2
                                          )
                               )
             )
    module OrderedCP = struct type t = csnum*snum 
                             let compare = Stdlib.compare
                             let to_string = bracketed_string_of_pair string_of_csnum string_of_snum
                      end
    module CPMap = MyMap.Make (OrderedCP)
    let memofunCP f s = 
      curry2 (CPMap.memofun id (uncurry2 (fun c s -> if !verbose || !verbose_qcalc then 
                                                       Printf.printf "%s (%s) (%s)\n" 
                                                                     s (string_of_csnum c) (string_of_snum s);
                                                     f c s
                                        )
                               )
             )

    let mcprod = memofunC2 cprod "cprod"
    let cprod (C (x1,y1) as c1) (C (x2,y2) as c2) = 
      match x1,y1, x2,y2 with
      | S_0     , S_0, _       , _    
      | _       , _  , S_0     , S_0       -> c_0
      | S_1     , S_0, _       , _         -> c2  
      | _       , _  , S_1     , S_0       -> c1
      | S_neg S_1, S_0, _       , _         -> cneg c2  
      | _       , _  , S_neg S_1, S_0       -> cneg c1
      | _                                  -> mcprod c1 c2
  
    let mcsum = memofunC2 csum "csum"
    let csum  (C (x1,y1) as c1) (C (x2,y2) as c2) = 
      match x1,y1, x2,y2 with
      | S_0, S_0, _  , _    -> c2 
      | _  , _  , S_0, S_0  -> c1
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

let make_snv ss = S_1, Array.of_list ss

let pcneg  (C (x,y)) = (* only for local use, please *)
  let negate = function
    | S_0 -> S_0
    | s   -> S_neg s
  in
  C (negate x, negate y) 

let pv_zero  = make_snv [c_1   ; c_0         ]
let pv_one   = make_snv [c_0   ; c_1         ]
let pv_plus  = make_snv [c_h   ; c_h         ]
let pv_minus = make_snv [c_h   ; pcneg c_h   ]

let pv_1 = make_snv [c_1] (* a unit for folding *)
let pv_0 = make_snv [c_0] (* another unit for folding *)

let string_of_matrix m = 
  let strings_of_row r = Array.fold_right (fun s ss -> string_of_csnum s::ss) r [] in
  let block = Array.fold_right (fun r ss -> strings_of_row r::ss) m [] in
  let rwidth r = List.fold_left max 0 (List.map String.length r) in
  let width = List.fold_left max 0 (List.map rwidth block) in
  let pad s = s ^ String.make (width - String.length s) ' ' in
  let block = String.concat "\n "(List.map (String.concat " " <.> List.map pad) block) in
  Printf.sprintf "\n{%s}\n" block
  
let string_of_cpad v =
  Printf.sprintf "diag{" ^ string_of_list string_of_csnum " " (Array.to_list v) ^ "}"
  
let make_m rows = rows |> (List.map Array.of_list) |> (Array.of_list)

let matrix_of_gate = function
  | MGate m -> m
  | DGate v -> let n = vsize v in
               let zs = Listutils.tabulate n (const c_0) in
               let rows = Listutils.tabulate n (const zs) in
               let m = make_m rows in
               for i = 0 to n-1 do
                 m.(i).(i) <- v.(i)
               done;
               m

(* this should only be used if it's really a unitary matrix *)               
let gate_of_matrix m =
  let n = rsize m in
  let isdiag = _for_all 0 1 n (fun i ->
                               let row = m.(i) in
                               _for_all 0 1 n (fun j -> i=j || row.(j)=c_0)
                              )
  in
  if isdiag then
    DGate (Array.init n (fun i -> m.(i).(i)))
  else MGate m
  
let make_g rows = 
  gate_of_matrix (make_m rows)

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
                     [c_0       ; C(S_f,S_g) ]]
                     
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
  let m = matrix_of_gate g in
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

let m_1 = make_m [[c_1]]
let m_0 = make_m [[c_0]]

(* the special Grover gate. Oh this is a filthy hack. *)
let groverG n =
  if n<1 || n>=20 then raise (Error (Printf.sprintf "grovergate %d" n)) else
  (let s = S_h (2*(n-1)) in
   let cp = c_of_p s in
   let size = 1 lsl n in
   let row _ = Array.init size (fun _ -> cp) in
   let m = Array.init size row in
   let s' = cdiff cp c_1 in
   for i=0 to size-1 do
     m.(i).(i) <- s'
   done;
   gate_of_matrix m
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
  gate_of_matrix m

(* ********************* string_of_ functions ***************************** *)

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
               | VMatrix m       -> string_of_matrix m
               | VGate g         -> string_of_gate g
               | VChar c         -> Printf.sprintf "'%s'" (Utf8.escaped c)
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
               | MGate m -> string_of_matrix m
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

