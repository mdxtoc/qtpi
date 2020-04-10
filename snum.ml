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

exception Disaster of string

(* h = sqrt (1/2) = cos (pi/4) = sin (pi/4); useful for rotation pi/4, or 45 degrees;
   f = sqrt ((1+h)/2) = cos (pi/8); useful for rotation pi/8 or 22.5 degrees;
   g = sqrt ((1-h)/2) = sin (pi/8); the partner of h;
   
   Note h^2 = 1/2; 
        f^2 = (1+h)/2 = h^2(1+h) = h^2+h^3;
        g^2 = (1-h)/2 = h^2(1-h) = h^2-h^3;
        fg  = sqrt ((1-h^2)/4) = sqrt(1/8) = sqrt(h^6) = h^3  
        
   Also f^2+g^2 = 1 (which will fall out of the above)
 *)

type snum = 
  | S_0
  | S_1
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
    | S_1
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
  | S_1             -> "1"
  | S_f             -> "f"
  | S_g             -> "g"
  | S_h 1           -> "h"
  | S_h n           -> Printf.sprintf "h(%d)" n
  | S_symb symb     -> string_of_s_symb symb 
  | S_neg s'         -> "-" ^ possbra s'
  | S_prod ss        -> String.concat "*" (List.map possbra ss)
  | S_sum  ss        -> sum_separate (List.map possbra ss)    

and string_of_s_symb symb =
    Printf.sprintf "%s%s%s%s" (if symb.alpha then "b" else "a") 
                              (string_of_int symb.id) 
                              (if symb.conj then "!" else "")
                              (if !showabvalues then let a, b = symb.secret in Printf.sprintf "[%f,%f]" a b else "")

and string_of_snums ss = bracketed_string_of_list string_of_snum ss

and string_of_snum_struct = function
              | S_0         -> "S_0"
              | S_1         -> "S_1"
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
    | S_1      -> "i"
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
  | []         -> raise (Can'tHappen "sum_separate []")

(* *********************** symbolic arithmetic ************************************ *)

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
    | S_1
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
          | S_1             , _                 -> s2
          | _               , S_1               -> s1
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
          | S_0     , _           -> s2
          | _       , S_0         -> s1
          | S_sum s1s, S_sum s2s  -> simplify_sum (s1s @ s2s)
          | _       , S_sum s2s   -> simplify_sum (s1 :: s2s)
          | S_sum s1s, _          -> simplify_sum (s2 :: s1s)
          | _                    -> simplify_sum [s1;s2]
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
                              | []  -> S_1
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

module SnumH = struct type t = snum 
                      let equal = (=)
                      let hash = Hashtbl.hash
                      let to_string = string_of_snum
               end
module SnumHash = MyHash.Make (SnumH)

let memofunProb f str = 
  let table = SnumHash.create 100 in
  SnumHash.memofun table (fun s -> if !verbose || !verbose_qcalc 
                                                     then Printf.printf "%s (%s)\n" str (string_of_snum s); 
                                                   f s
                                         )

let memofun2Prob f str = 
  let t1 = SnumHash.create 100 in
  SnumHash.memofun t1 
    (fun s1 -> let t2 = SnumHash.create 100 in
               SnumHash.memofun t2 
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

let csnum_of_snum s = C (s, S_0)

let c_0 = csnum_of_snum S_0
let c_1 = csnum_of_snum S_1
let c_h = csnum_of_snum (S_h 1)
let c_f = csnum_of_snum S_f
let c_g = csnum_of_snum S_g

let c_i = C (S_0, S_1)

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
  | S_0     , S_0, _       , _    
  | _       , _  , S_0     , S_0       -> c_0
  | S_1     , S_0, _       , _         -> c2  
  | _       , _  , S_1     , S_0       -> c1
  | S_neg S_1, S_0, _       , _        -> cneg c2  
  | _       , _  , S_neg S_1, S_0      -> cneg c1
  | _       , S_0, _       , S_0       -> intern (C (rprod x1 x2, S_0))            (* real    * real    *)
  | _       , S_0, _       , _         -> intern (C (rprod x1 x2, rprod x1 y2))    (* real    * complex *)
  | _       , _  , _       , S_0       -> intern (C (rprod x1 x2, rprod y1 x2))    (* complex * real    *)
  | _                                  -> intern (C (rsum (rprod x1 x2) (rneg (rprod y1 y2)), rsum (rprod x1 y2) (rprod y1 x2)))

let csum  (C (x1,y1) as c1) (C (x2,y2) as c2) = 
  match x1,y1, x2,y2 with
  | S_0, S_0, _  , _    -> c2 
  | _  , _  , S_0, S_0  -> c1
  | _                   -> intern (C (rsum x1 x2, rsum y1 y2))

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

