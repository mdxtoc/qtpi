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

type snum = 
  | S_0
  | S_1
  | S_f              
  | S_g 
  | S_h of int              
  | S_symb of int * bool * float     (* k, false=a_k, true=b_k, both random floats s.t. a_k**2+b_k**2 = 1; random r s.t. 0<=r<=1.0 *)
  | S_neg of snum
  | S_prod of snum list              (* associative *)
  | S_sum of snum list               (* associative *)

and s_symb = { id: int; alpha: bool; conj: bool; secret: float ref}

(* S_symb is an unknown (with furtively a secret value -- see below). 
   0, 1, f and g are reals, but S_symb is a complex number. So it has a conjugate. 
   Hence the normal field.
   
   The order of the fields matters for sorting: 
    -- a1 comes before a2 (and b2, and etc.) so the id field is first; 
    -- ai comes before bi so the alpha field is second (and false means a);
    -- ai comes before ai! so the conj field is third;
    -- occurrences of ai with the same i have the same secret value.
    
    The secret value is used when measuring, to compute the value of a formula
    involving the symbol. It is _never_ used when calculating/simplifying, even if
    it is 0.0 or 1.0 (which it very very rarely might be).
 *)

and csnum = C of snum*snum (* complex snum A + iB *)

and modulus = snum

(* snv: symbolic normalised vector *)
and snv = modulus * csnum array (* modulus, vector: written as 1/sqrt(modulus)(vec) *)

let vsize = Array.length
let snvsize (_,v) = vsize v
let rsize = Array.length
let csize m = vsize m.(0)

let rec string_of_snum p = 
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
  let possbra p' = 
    let supprio = prio p in
    let subprio = prio p' in
    let s = string_of_snum p' in
    if subprio<=supprio then "!!(" ^ s ^ ")!!" else s
  in
  match p with
  | S_0             -> "0"
  | S_1             -> "1"
  | S_f             -> "f"
  | S_g             -> "g"
  | S_h 1           -> "h"
  | S_h n           -> Printf.sprintf "h(%d)" n
  | S_symb (q,b,f)   -> Printf.sprintf "%s%s%s" (if b then "b" else "a") (string_of_int q) 
                                                (if !showabvalues then Printf.sprintf "[%f]" f else "")
  | S_neg p'         -> "-" ^ possbra p'
  | S_prod ps        -> String.concat "*" (List.map possbra ps)
  | S_sum  ps        -> sum_separate (List.map possbra ps)    

and string_of_csnum (C (x,y)) =
  let im y = 
    match y with
    | S_1     -> "i"
    | S_f  
    | S_g 
    | S_h   _ 
    | S_symb _ 
    | S_prod _ -> "i*" ^ string_of_snum y
    | _       -> "i*(" ^ string_of_snum y ^ ")"
  in
  match x,y with
  | S_0, S_0    -> "0"
  | _  , S_0    -> string_of_snum x
  | S_0, S_neg p -> "-" ^ im p
  | S_0, _      -> im y
  | _  , S_neg p -> "(" ^ string_of_snum x ^ "-" ^ im p ^ ")"
  | _  , _      -> "(" ^ string_of_snum x ^ "+" ^ im y ^ ")"

and sum_separate = function
  | p1::p2::ps -> if Stringutils.starts_with p2 "-" then p1 ^ sum_separate (p2::ps) 
                  else p1 ^ "+" ^ sum_separate (p2::ps) 
  | [p]        -> p
  | []         -> raise (Can'tHappen "sum_separate []")

type bksign = PVBra | PVKet

let string_of_snv bksign = 
  let so_snv v =
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
         (* all but simple real sums are bracketed in string_of_csnum *)
         match real, im with
         | S_sum _, S_0 -> true
         | _           -> false
       in
       let estrings = _for_leftfold 0 1 n
                        (fun i ss -> match string_of_csnum v.(i) with
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
       | []  -> "??empty snv??"
       | [e] -> e
       | _   -> Printf.sprintf "(%s)" (sum_separate (List.rev estrings))
      )
    else
      (let estrings = Array.fold_right (fun p ss -> string_of_csnum p::ss) v [] in
       Printf.sprintf "(%s)" (String.concat " <,> " estrings)
      )
  in
  function
  | S_1, vv -> so_snv vv
  | vm , vv -> Printf.sprintf "<<%s>>%s" (string_of_snum vm) (so_snv vv)
  
let string_of_bra = string_of_snv PVBra
let string_of_ket = string_of_snv PVKet
