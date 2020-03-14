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

(* h = sqrt (1/2) = cos (pi/4) = sin (pi/4); useful for rotation pi/4, or 45 degrees;
   f = sqrt ((1+h)/2) = cos (pi/8); useful for rotation pi/8 or 22.5 degrees;
   g = sqrt ((1-h)/2) = sin (pi/8); the partner of h;
   
   Note h^2 = 1/2; 
        f^2 = (1+h)/2 = h^2(1+h) = h^2+h^3;
        g^2 = (1-h)/2 = h^2(1-h) = h^2-h^3;
        fg  = sqrt ((1-h^2)/4) = sqrt(1/8) = sqrt(h^6) = h^3  
        
   Also f^2+g^2 = 1 (which will fall out of the above)
 *)
type prob = 
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

let vsize = Array.length
let pvsize (p,v) = vsize v

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

and sum_separate = function
  | p1::p2::ps -> if Stringutils.starts_with p2 "-" then p1 ^ sum_separate (p2::ps) 
                  else p1 ^ "+" ^ sum_separate (p2::ps) 
  | [p]        -> p
  | []         -> raise (Can'tHappen "sum_separate []")

type bksign = PVBra | PVKet

let string_of_probvec bksign = 
  let so_pv v =
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
         Printf.sprintf (match bksign with PVBra -> "<%s|" | PVKet -> "|%s>") (string_of_bin i)
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
  in
  function
  | P_1, vv -> so_pv vv
  | vm , vv -> Printf.sprintf "<<%s>>%s" (string_of_prob vm) (so_pv vv)
  

