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
open Forutils
open Listutils
open Optionutils
open Functionutils
open Tupleutils
open Number

exception Disaster of string

(* some random things to do with bits of zints *)

(* bits set in a zint -- positive only *)
let setbits : zint -> int list = fun n ->
  let rec sb bs k n =
    if n=:z_0 then List.rev bs 
              else sb Z.(if (n mod z_2 = z_0) then bs else k::bs) (k+1) Z.(n asr 1)
  in
  if Z.(n<zero) then raise (Invalid_argument ("setbits " ^ string_of_zint n))
                else sb [] 0 n 
  
(* find log_2 n, but only if n is a power of 2 -- else raise Invalid_argument *)
let log_2 : zint -> int = fun n ->
  match setbits n with
  | [k] -> k
  | _   -> raise (Invalid_argument ("log_2 " ^ string_of_zint n))

(* ***************** Symbolic numbers, used as amplitudes and probabilities ************************** *)

(* h = sqrt (1/2) = cos (pi/4) = sin (pi/4); useful for rotation pi/4, or 45 degrees;
   f = sqrt ((1+h)/2) = cos (pi/8); useful for rotation pi/8 or 22.5 degrees;
   g = sqrt ((1-h)/2) = sin (pi/8); the partner of f;
   
   Note h^2 = 1/2; 
        f^2 = (1+h)/2 = h^2(1+h) = h^2+h^3;
        g^2 = (1-h)/2 = h^2(1-h) = h^2-h^3;
        fg  = sqrt ((1-h^2)/4) = sqrt(1/8) = sqrt(h^6) = h^3  
        
   Also f^2+g^2 = 1 (which will fall out of the above)
 *)

type snum = (* no S_1: h is now allowed neg and zero powers. So 1 is S_h 0 *)
  | S_0
  | S_f              
  | S_g 
  | S_h    of int              
  | S_symb of s_symb                 (* k, false=a_k, true=b_k, conjugated, both random floats s.t. a_k**2+b_k**2 = 1; random r s.t. 0<=r<=1.0 *)
  | S_neg  of snum
  | S_prod of snum list              (* associative *)
  | S_sum  of snum list              (* associative *)

and s_symb = { id: int; alpha: bool; conj: bool; secret: float*float}

(* S_symb is an unknown (with furtively a secret value -- see below). 
   0, 1, f and g are reals, but S_symb is a complex number. So it has a conjugate. 
   Hence the normal field.
   
   The order of the fields matters for sorting: 
    -- a1 comes before a2 (and b2, and etc.) so the id field is first; 
    -- ai comes before bi so the alpha field is second (and false means a);
    -- ai comes before ai! so the conj field is third;
    -- a secret amplitude value.
    
    The secret values are used when measuring, to compute the value of a formula
    involving the symbol. They are _never_ used when calculating/simplifying, even if
    it is 0.0 or 1.0 (which it very very rarely might be).
    
    We need both floats -- one for a, one for b -- because of a2b2.
 *)

and csnum = C of snum*snum (* complex snum A + iB *)

let rec string_of_snum s = 
  (* Everything is associative, but the normal form is sum of negated products.
   * So possbra below puts in _very_ visible brackets, for diagnostic purposes.
   *)
  let prio = function
    | S_0
    | S_f  
    | S_g 
    | S_h  _ 
    | S_symb _         -> 10
    | S_prod _         -> 8
    | S_neg  _         -> 6
    | S_sum  _         -> 4
  in
  let possbra s' = 
    let supprio = prio s in
    let subprio = prio s' in
    let s = string_of_snum s' in
    if subprio<=supprio then "!!(" ^ s ^ ")!!" else s
  in
  match s with
  | S_0             -> "0"
  | S_f             -> "f"
  | S_g             -> "g"
  | S_h 0           -> "1"
  | S_h 1           -> "h"
  | S_h n           -> Printf.sprintf "h(%d)" n
  | S_symb symb     -> string_of_s_symb symb 
  | S_neg s'         -> "-" ^ possbra s'
  | S_prod ss        -> String.concat "*" (List.map possbra ss)
  | S_sum  ss        -> sum_separate (List.map possbra ss)    

and string_of_s_symb symb =
    Printf.sprintf "%s%s%s%s" (if symb.alpha then "b" else "a") 
                              (string_of_int symb.id) 
                              (if symb.conj then "†" else "")
                              (if !showabvalues then let a, b = symb.secret in Printf.sprintf "[%f,%f]" a b else "")

and string_of_snums ss = bracketed_string_of_list string_of_snum ss

and string_of_snum_struct = function
              | S_0         -> "S_0"
              | S_f         -> "S_f"
              | S_g         -> "S_g"
              | S_h i       -> Printf.sprintf "S_h %d" i             
              | S_symb symb -> Printf.sprintf "S_symb %s" (string_of_s_symb_struct symb)
              | S_neg  s    -> Printf.sprintf "S_neg (%s)" (string_of_snum_struct s)
              | S_prod ss   ->  Printf.sprintf "S_prod (%s)" (string_of_snum_structs ss)
              | S_sum  ss   ->  Printf.sprintf "S_sum (%s)" (string_of_snum_structs ss)

and string_of_snum_structs ss = bracketed_string_of_list (string_of_snum_struct) ss

and string_of_s_symb_struct symb =
    let a,b = symb.secret in
    Printf.sprintf "{id=%d; alpha=%B;%s secret=(%f,%f)}" 
                              symb.id symb.alpha (if !complexunknowns then Printf.sprintf " conj=%B;" symb.conj else "") a b

and string_of_csnum (C (x,y)) =
  let im y = 
    match y with
    | S_h 0    -> "i"
    | S_f  
    | S_g 
    | S_h   _ 
    | S_symb _ 
    | S_prod _ -> "i*" ^ string_of_snum y
    | _        -> "i*(" ^ string_of_snum y ^ ")"
  in
  match x,y with
  | S_0, S_0     -> "0"
  | _  , S_0     -> string_of_snum x
  | S_0, S_neg s -> "-" ^ im s
  | S_0, _       -> im y
  | _  , S_neg s -> "(" ^ string_of_snum x ^ "-" ^ im s ^ ")"
  | _  , _       -> "(" ^ string_of_snum x ^ "+" ^ im y ^ ")"

and sum_separate = function
  | s1::s2::ss -> if Stringutils.starts_with s2 "-" then s1 ^ sum_separate (s2::ss) 
                  else s1 ^ "+" ^ sum_separate (s2::ss) 
  | [s]        -> s
  | []         -> "0" (* oh yes it can happen ... raise (Can'tHappen "sum_separate []") *)

(* *********************** symbolic arithmetic ************************************ *)

(* The normal form is a sum of possibly-negated products. 
 * Both sums and products are left-recursive.
 * Products are sorted according to the type definition: i.e.
 * S_0, S_f, S_g, S_h, S_symb. But ... this isn't good enough. 
 
 * We need to sort identifiers according to their suffix: a0,b0,a1,b1, ...
 
 * Stdlib.compare works if we change the definition of S_symb, so I did
 
 *)

(* let compare s1 s2 =
     match s1, s2 with
     | S_symb (b1,q1,_), S_symb (b2,q2,_) -> Stdlib.compare (q1,b1) (q2,b2)
     | _                                  -> Stdlib.compare s1      s2
*)
(* we deal with long lists. Avoid sorting if poss *)
let sort compare ss =
  let rec check ss' =
    match ss' with
    | s'::(s''::_ as ss') -> if s'<s'' then check ss' else List.sort compare ss
    | _                   -> ss
  in
  check ss

(* an snum is usually a real. But not always ... *)
let rconj s = 
  let rec rc = function
    | S_0
    | S_f              
    | S_g 
    | S_h    _      -> None
    | S_symb symb   -> Some (S_symb {symb with conj=not symb.conj})
    | S_neg  s      -> rc s &~~ (fun s' -> Some (S_neg s'))
    | S_prod ss     -> optmap_any rc ss &~~ (fun ss' -> Some (S_prod ss'))
    | S_sum  ss     -> optmap_any rc ss &~~ (fun ss' -> Some (S_sum ss'))
  in
  if !complexunknowns then (rc ||~ id) s else s
  
let rec rneg s =
  let r = match s with
          | S_neg s     -> s
          | S_0         -> s
          | S_sum ss    -> simplify_sum (List.map rneg ss)
          | _           -> S_neg s
  in
  if !verbose_simplify then
    Printf.printf "rneg (%s) -> %s\n" (string_of_snum s) (string_of_snum r);
  r
    
and rprod s1 s2 =
  let r = match s1, s2 with
          | S_0             , _
          | _               , S_0               -> S_0
          | S_h 0           , _                 -> s2
          | _               , S_h 0             -> s1
          | S_neg s1         , _                -> rneg (rprod s1 s2)
          | _               , S_neg s2          -> rneg (rprod s1 s2)
          | _               , S_sum s2s         -> let ss = List.map (rprod s1) s2s in
                                                   simplify_sum (sflatten ss)
          | S_sum s1s       , _                 -> let ss = List.map (rprod s2) s1s in
                                                   simplify_sum (sflatten ss)
          | S_prod s1s      , S_prod s2s        -> simplify_prod (s1s @ s2s)
          | _               , S_prod s2s        -> simplify_prod (s1 :: s2s)
          | S_prod s1s      , _                 -> simplify_prod (s2::s1s)
          | _                                   -> simplify_prod [s1;s2]
  in
  if !verbose_simplify then
    Printf.printf "rprod (%s) (%s) -> %s\n" (string_of_snum s1) (string_of_snum s2) (string_of_snum r);
  r

and make_prod = function
  | [s] -> s
  | []  -> S_h 0
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
            | S_h 0          :: ss -> sp r ss
            | S_f   :: S_f   :: ss -> premult (S_sum [S_h 2; S_h 3]) ss
            | S_f   :: S_g   :: ss -> premult (S_h 3) ss
            | S_g   :: S_g   :: ss -> premult (S_sum [S_h 2; S_neg (S_h 3)]) ss
(*          | S_g   :: S_h i :: ss    (* prefer f to g: gh^3 is gfg = fg^2 *)
              when i>=3            -> sp (S_f :: r) (S_g :: S_g :: (ihs (i-3) ss)) 
 *)
            | S_g   :: S_h i :: ss    (* prefer f to g: gh^3 is gfg = fg^2 = f(h^2-h^3) so gh = f(1-h) *)
              when i>=1            -> premult (S_sum [S_h 0; S_neg (S_h 1)]) (S_f :: (ihs (i-1) ss))
            | S_h i :: S_h j :: ss -> sp (ihs (i+j) r) ss
            | s              :: ss -> sp (s::r) ss
            | []                   -> None, List.rev r
          in
          let popt, ss = sp [] (sort Stdlib.compare ss) in
          let s = match ss with 
                  | []  -> S_h 0
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
          | S_0      , _          -> s2
          | _        , S_0        -> s1
          | S_sum s1s, S_sum s2s  -> simplify_sum (s1s @ s2s)
          | _        , S_sum s2s  -> simplify_sum (s1 :: s2s)
          | S_sum s1s, _          -> simplify_sum (s2 :: s1s)
          | _                     -> simplify_sum [s1;s2]
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
  let r = let rec sumcompare s1 s2 = (* ignore negation, but put -s after s *)
            match s1, s2 with
            | S_neg s1  , S_neg s2   -> sumcompare s1 s2
            | S_neg s1  , _          -> let r = sumcompare s1 s2 in if r=0 then 1 else r (* put -s after s *)
            | _         , S_neg s2   -> sumcompare s1 s2
         (* | S_prod s1s, S_prod s2s -> Stdlib.compare s1s s2s *)
            | _                      -> Stdlib.compare s1 s2
          in
          let rec multiple s1 rest = (* looking for X+X+... -- we no longer care about the h's *)
            let r = (match takedropwhile ((=)s1) rest with
                     | [] , _    -> None (* not going to happen, but never mind *)
                     | s1s, rest -> Some (rmult_zint s1 (Z.of_int (List.length s1s+1)), rest)
                    )
            in
            if !verbose_simplify then
              Printf.printf "multiple (%s) %s -> %s\n" (string_of_snum s1)  
                                                       (bracketed_string_of_list string_of_snum rest)
                                                       (string_of_option (string_of_pair string_of_snum (bracketed_string_of_list string_of_snum) ",") r);
            r
          in
          let rec a2b2 s ss = (* looking for X*aa!Y+X*bb!Y to replace with XY. Sorting doesn't put pairs next to each other always *)
            let search neg sps =
              let rec find pres sps =
                match sps with 
                | S_symb ({id=q1; alpha=false; conj=false} as symb1) :: 
                  S_symb ({id=q2; alpha=false; conj=c    } as symb2) :: sps 
                            when q1=q2 && c = !complexunknowns 
                            -> 
                    let remake post =
                      let r = match prepend pres post with 
                              | []  -> S_h 0
                              | [s] -> s
                              | ss  -> S_prod ss
                      in
                      if neg then S_neg r else r
                    in
                    let s' = remake (S_symb {symb1 with alpha=true} :: S_symb {symb2 with alpha=true} :: sps) in
                    if !verbose_simplify then 
                      Printf.printf "a2b2.find looking for %s in %s\n" (string_of_snum s') (string_of_snums ss);
                    if List.exists ((=) s') ss then Some (remake sps, Listutils.remove s' ss)
                                               else find (S_symb symb2::S_symb symb1::pres) sps
                | s :: sps  -> find (s::pres) sps
                | _         -> None
              in
              find [] sps
            in
            let r = match s with
                    | S_neg (S_prod sps) -> search true  sps 
                    | S_prod sps         -> search false sps
                    | _                  -> None
            in
            if !verbose_simplify then
              Printf.printf "a2b2 (%s) %s -> %s\n" (string_of_snum s) (string_of_snums ss)  
                                                   (string_of_option (bracketed_string_of_pair string_of_snum string_of_snums) r);
            r
          in
          let rec sp again r ss =
            if !verbose_simplify then 
              Printf.printf "sp %B %s %s\n" again (string_of_snums r) (string_of_snums ss);
            match ss with
            | S_0                 :: ss            -> sp true r ss
            | S_neg s1 :: s2      :: ss when s1=s2 -> sp true r ss
            | s1      :: S_neg s2 :: ss when s1=s2 -> sp true r ss
            (* the next lot are because h^j-h^(j+2) = h^j(1-h^2) = h^(j+2) 
               If it all works then we should allow also for j=0, and the whole mess
               prefixed with f (but not g, because of simplify_prod).
             *)
            (* and for confluence, dammit, I have to do the h(j)+h(j+2) = h(j-2)-h(j+2) thing. Rats. *)
            | S_h j      ::  ss  
                    when List.exists ((=) (S_neg (S_h (j+2)))) ss
                                                  -> sp true (S_h (j+2)::r) (Listutils.remove (S_neg (S_h (j+2))) ss)
            | S_h j      ::  ss  
                    when List.exists ((=) (S_h (j+2))) ss
                                                  -> sp true (S_neg (S_h (j+2))::S_h (j-2)::r) (Listutils.remove (S_h (j+2)) ss)
            | S_neg (S_h j) :: ss  
                    when List.exists ((=) (S_h (j+2))) ss  
                                                  -> sp true (S_neg (S_h (j+2))::r) (Listutils.remove (S_h (j+2)) ss)
            | S_neg (S_h j) :: ss  
                    when List.exists ((=) (S_neg (S_h (j+2)))) ss  
                                                  -> sp true (S_h (j+2)::S_neg (S_h (j-2))::r) (Listutils.remove (S_neg (S_h (j+2))) ss)
            | S_prod (S_h j :: s1s) :: ss
                    when List.exists ((=) (S_neg (S_prod (S_h (j+2) :: s1s)))) ss                 
                                                  -> sp true (S_prod (S_h (j+2) :: s1s)::r) 
                                                             (Listutils.remove (S_neg (S_prod (S_h (j+2) :: s1s))) ss)
            | S_prod (S_h j :: s1s) :: ss
                    when List.exists ((=) (S_prod (S_h (j+2) :: s1s))) ss                 
                                                  -> sp true (S_neg (S_prod (S_h (j+2) :: s1s))::(S_prod (S_h (j-2) :: s1s))::r) 
                                                             (Listutils.remove (S_prod (S_h (j+2) :: s1s)) ss)
            | S_neg (S_prod (S_h j :: s1s)) :: ss
                    when List.exists ((=) (S_prod (S_h (j+2) :: s1s))) ss                 
                                                  -> sp true (S_neg (S_prod (S_h (j+2) :: s1s)) :: r) 
                                                             (Listutils.remove (S_prod (S_h (j+2) :: s1s)) ss)
            | S_neg (S_prod (S_h j :: s1s)) :: ss
                    when List.exists ((=) (S_neg (S_prod (S_h (j+2) :: s1s)))) ss                 
                                                  -> sp true (S_prod (S_h (j+2) :: s1s) :: S_neg (S_prod (S_h (j-2) :: s1s)) :: r) 
                                                             (Listutils.remove (S_prod (S_h (j+2) :: s1s)) ss)
            (* the next four are backwards ... *)
            | (S_prod (S_h 2 :: s1s) as s1) :: ss  
                   when List.exists ((=) (S_neg (make_prod s1s))) ss 
                                                  -> sp true (S_neg s1::r) (Listutils.remove (S_neg (make_prod s1s)) ss)
            | (S_prod (S_h 2 :: s1s) as s1) :: ss  
                   when List.exists ((=) (make_prod s1s)) ss 
                                                  -> sp true (S_neg s1::S_prod (S_h (-2) :: s1s)::r) (Listutils.remove (S_neg (make_prod s1s)) ss)
            | (S_neg (S_prod (S_h 2 :: s1s) as s1)) :: ss  
                   when List.exists ((=) (make_prod s1s)) ss  
                                                  -> sp true (s1::r) (Listutils.remove (make_prod s1s) ss)
            | (S_neg (S_prod (S_h 2 :: s1s) as s1)) :: ss  
                   when List.exists ((=) (S_neg (make_prod s1s))) ss  
                                                  -> sp true (s1::S_neg (S_prod (S_h (-2) :: s1s))::r) (Listutils.remove (S_neg (make_prod s1s)) ss)
            (* and no more about hs for a while *)
            | S_prod (S_f :: S_h (-1) :: s1s) :: ss
                   when List.exists ((=) (S_neg (make_prod (S_f :: s1s)))) ss
                                                  -> sp true (make_prod (S_g :: s1s) :: r) 
                                                             (Listutils.remove (S_neg (make_prod (S_f :: s1s))) ss)
            | S_neg (S_prod (S_f :: S_h (-1) :: s1s)) :: ss
                   when List.exists ((=) (make_prod (S_f :: s1s))) ss
                                                  -> sp true (S_neg (make_prod (S_g :: s1s)) :: r) 
                                                             (Listutils.remove (make_prod (S_f :: s1s)) ss)
            | s1      :: s2      :: ss when s1=s2 -> (match multiple s1 (s2::ss) with
                                                      | Some (s,ss) -> sp true (s::r) ss
                                                      | None        -> sp again (s1::r) (s2::ss)
                                                     )
            | s                  :: ss            -> (match a2b2 s ss with
                                                      | Some (s, ss) -> sp true (s::r) ss
                                                      | None         -> sp again (s::r) ss
                                                     )
            | []                                  -> let r = List.rev r in
                                                     if again then doit (sflatten r) else r
          and doit ss = sp false [] (sort sumcompare ss)
          in
          if List.exists (function S_sum _ -> true | S_neg (S_sum _) -> true | _ -> false) ss then
            raise (Error (Printf.sprintf "simplify_sum (%s)" (string_of_snum (S_sum ss))))
          else
          match doit ss with
          | []  -> S_0
          | [s] -> s
          | ss  -> S_sum (sort sumcompare ss)
  in
  if !verbose_simplify then
    Printf.printf "simplify_sum (%s) -> %s\n" (string_of_snum (S_sum ss)) (string_of_snum r);
  r

and rmult_zint sn zi =
  if sn=S_0 || Z.(zi=zero) then S_0 else
  if Z.(zi<zero) then rneg (rmult_zint sn Z.(~-zi))
                 else match setbits zi with
                      | []  -> S_0
                      | [0] -> sn
                      | bs  -> rprod sn (S_sum (List.map (fun i -> S_h (-2*i)) bs))
  
and sqrt_half i =   (* (1/sqrt 2)**i *)
  let r = if i=0 then S_h 0 else S_h i in
  if !verbose_simplify then
    Printf.printf "sqrt_half %d -> %s\n" i (string_of_snum r);
  r

and rdiv_h s = rprod (S_h (-1)) s (* multiply by h(-1) (= divide by h(1)). Happens: see normalise *)
  
(******** snum arithmetic is where all the action is. So we memoise sum and prod, carefully *********)

module SnumH = struct type t = snum 
                      let equal = (=)
                      let hash = Hashtbl.hash
                      let to_string = string_of_snum
               end
module SnumHash = MyHash.Make (SnumH)

let memofunProb f str = 
  let table = SnumHash.create 100 in
  SnumHash.memofun table (fun s -> if !verbose || !verbose_simplify 
                                                     then Printf.printf "memofun %s (%s)\n" str (string_of_snum s); 
                                                   f s
                                         )

let memofun2Prob f str = 
  let t1 = SnumHash.create 100 in
  SnumHash.memofun t1 
    (fun s1 -> let t2 = SnumHash.create 100 in
               SnumHash.memofun t2 
                 (fun s2 -> let r = f s1 s2 in
                            if !verbose || !verbose_simplify 
                            then Printf.printf "memofun2 %s (%s) (%s) -> %s\n" 
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
    | S_h 0     , _     -> s2
    | _       , S_h 0   -> s1
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
   (* (* we memoise sum *)
    | S_sum  _ , _
    | _       , S_sum  _ -> memo_rsum s1 s2
    (* everything else is raw *)
    | _                 -> raw_rsum s1 s2 *)
    | _                -> memo_rsum s1 s2
  else
    raw_rsum s1 s2
  
(* *********************** complex arith in terms of reals ************************************ *)

let csnum_of_snum s = C (s, S_0)

let c_0 = csnum_of_snum S_0
let c_1 = csnum_of_snum (S_h 0)
let c_h = csnum_of_snum (S_h 1)
let c_f = csnum_of_snum S_f
let c_g = csnum_of_snum S_g

let c_i = C (S_0, S_h 0)

module CsnumH = struct type t = csnum
                      let equal = (=)
                      let hash = Hashtbl.hash
                      let to_string = string_of_csnum
               end
module CsnumHash = MyHash.Make (CsnumH)

(* maybe this will save some space ... *)
let interntab = CsnumHash.create 1000
let intern cn = try CsnumHash.find interntab cn with Not_found -> (CsnumHash.add interntab cn cn; cn)

let cneg  (C (x,y)) = intern (C (rneg x, rneg y))

let cprod (C (x1,y1) as c1) (C (x2,y2) as c2) = 
  match x1,y1, x2,y2 with
  | S_0          , S_0, _            , _    
  | _            , _  , S_0          , S_0       -> c_0
  | S_h 0        , S_0, _            , _         -> c2  
  | _            , _  , S_h 0        , S_0       -> c1
  | S_neg (S_h 0), S_0, _            , _         -> cneg c2  
  | _            , _  , S_neg( S_h 0), S_0       -> cneg c1
  | _            , S_0, _            , S_0       -> intern (C (rprod x1 x2, S_0))            (* real    * real    *)
  | _            , S_0, _            , _         -> intern (C (rprod x1 x2, rprod x1 y2))    (* real    * complex *)
  | _            , _  , _            , S_0       -> intern (C (rprod x1 x2, rprod y1 x2))    (* complex * real    *)
  | _                                            -> intern (C (rsum (rprod x1 x2) (rneg (rprod y1 y2)), rsum (rprod x1 y2) (rprod y1 x2)))

let csum  (C (x1,y1) as c1) (C (x2,y2) as c2) = 
  match x1,y1, x2,y2 with
  | S_0, S_0, _  , _    -> c2 
  | _  , _  , S_0, S_0  -> c1
  | _                   -> intern (C (rsum x1 x2, rsum y1 y2))

let simplify_csum = function
  | [] -> c_0
  | cs -> let reals, ims = List.split (List.map (fun (C (x,y)) -> x,y) cs) in
          C (simplify_sum (sflatten reals), simplify_sum (sflatten ims))  

let cdiff c1 c2 = csum c1 (cneg c2)

let cconj (C(x,y)) = intern (C (rconj x, rneg (rconj y)))

let absq  (C(x,y) as c) = (* this is going to cost me ... *)
  let x',y' = rconj x, rconj y in
  if x=x' && y=y' || y=S_0 then rsum (rprod x x') (rprod y y')
  else (let c' = cconj c in 
        if !verbose || !verbose_simplify then
          Printf.printf "**Here we go: |%s|^2 is (%s)*(%s)\n"
                              (string_of_csnum c)
                              (string_of_csnum c)
                              (string_of_csnum c');
        let C(rx,ry) as r = cprod c c' in
        if ry=S_0 then (if !verbose || !verbose_simplify then Printf.printf "phew! that worked -- %s\n" (string_of_snum rx); 
                        rx
                       )
        else raise (Disaster (Printf.sprintf "|%s|^2 is (%s)*(%s) = %s"
                                              (string_of_csnum c)
                                              (string_of_csnum c)
                                              (string_of_csnum c')
                                              (string_of_csnum r)
                             )
                   )
       )

(* we can't really divide 
    let c_r_div   (C(x,y)) z          = C (rdiv x z, rdiv y z)
 *)
let c_r_div_h (C(x,y))            = intern (C (rdiv_h x, rdiv_h y))

let cmult_zint (C(x,y)) zi        = intern (C (rmult_zint x zi, rmult_zint y zi))

(* we no longer memoise any complex arithmetic functions ...

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
      | S_0          , S_0, _            , _    
      | _            , _  , S_0          , S_0       -> c_0
      | S_h 0        , S_0, _            , _         -> c2  
      | _            , _  , S_h 0        , S_0       -> c1
      | S_neg (S_h 0), S_0, _            , _         -> cneg c2  
      | _            , _  , S_neg (S_h 0), S_0       -> cneg c1
      | _                                            -> mcprod c1 c2
  
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

