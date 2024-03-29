(*
    This is Richard Bornat's modified version of Bernard Sufrin's 
    number.ml, taken on 2018/11/28 from his picoml implementation 
    (not yet published)
    
*)

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

(*
        Number representation
        
        It would be straightforward to add a plethora of representations here, but
        we have limited ourselves just to unbounded-precision rationals.
        
        (Says Bernard. Straightforward, nothing.)
        
*)

open Functionutils

type num = Q.t
type zint = Z.t
module Local = struct
 
  let splat: string -> char -> string * string =
   fun s c -> 
   let p = String.rindex s c in (String.sub s 0 p, String.sub s (p+1) (String.length s-p-1))

  open Q
  open String
  let (>=) = Stdlib.(>=) (* don't pick up Q.(>=) from zarith 1.9.1 etc. *)
  
  let ( // )=div
  let ( */ )=mul
  let ( -/ )=sub
  let ( +/ )=add
 
  let z_0        : Z.t = Z.zero
  let z_1        : Z.t = Z.one
  let z_2        : Z.t = Z.of_string "2"
  let z_3        : Z.t = Z.of_string "3"
  let z_10       : Z.t = Z.of_string "10"
 
  let pow10: int -> Z.t = fun exp -> Z.pow z_10 exp
 
  let qpow10: int -> num = 
          fun exp -> 
              if exp>=0 then 
                 Q.make (pow10(exp)) z_1
              else
                 Q.make z_1 (pow10(Stdlib.abs exp)) 

  let fraction s = Q.make (Z.of_string s) (pow10 (String.length s))
  let exponent s = qpow10 (int_of_string s)

  let rec num_of_string : string -> num =
  fun s -> 
    try let (n, f) = splat s 'e' in num_of_string n */ exponent f
    with
    Not_found -> 
    try let (n, f) = splat s 'E' in num_of_string n */ exponent f
    with
    Not_found -> 
    try let (n, f) = splat s '.' in num_of_string n +/ fraction f
    with
    Not_found -> Q.of_string s
   
  let prec = ref 0
  let pr   = ref Q.to_string 
 
  let string_of_num n =  !pr n
 
  let set_print_precision n =
     prec:= Q.to_int n;
     match !prec with
     |  0 -> pr := Q.to_string
     |  n -> pr := (fun q -> string_of_float (Q.to_float q))
            (* WAS:
             if n>0 then
                pr := approx_num_fix n
             else
                pr := approx_num_exp (-n)
             *)
   
  let floor: num -> zint =
      fun n -> Z.fdiv n.num n.den
  
  let ceiling: num -> zint =
      fun n -> Z.cdiv n.num n.den

  (* let integer: num -> num =
         fun n ->
         let num = Z.abs n.num
         and den = Z.abs n.den
         in 
           match sign n with
           | 0    -> n
           | 1    -> Q.make (Z.div num den) z_1
           | _    -> Q.make (Z.div num den) Z.minus_one (* sign n = -1 *)
   
    *)  
  
  let zint_of_num: num -> zint = 
    Q.to_bigint
    
  let num_of_zint: zint -> num =
    fun zi -> Q.make zi z_1
    
  let rem: num -> num -> num =  
    fun a -> fun b -> 
      let a = zint_of_num a in
      let b = zint_of_num b in
      num_of_zint (Z.rem a b)
      
  let numden: num -> (num*num) =
      fun n ->
      let num = Q.make n.num z_1
      and den = Q.make n.den z_1
      in (num, den)

  (* div_rem and div_mod are weird, but I think they make sense. 
     How many (a/b)s are there in (c/d)? Convert to same denominator:
     How many (ad/bd)s are there in (bc/bd)? 
     Answer bc div ad, remainder (bc rem ad)/bd
       -- with adjustments for the meaning of div and rem.
     
   *) 
  let divrem: (zint -> zint -> (zint*zint)) -> num -> num -> (zint*num) = 
    fun divrem cd ab -> 
      let a = ab.num in
      let b = ab.den in
      let c = cd.num in
      let d = cd.den in
      let q,r = divrem Z.(b*c) Z.(a*d) in
      let r = Q.make r Z.(b*d) in
      (q, r)
  
  let div_rem: num -> num -> (zint*num) = divrem Z.div_rem
  let div_mod: num -> num -> (zint*num) = divrem Z.ediv_rem
   
  let is_int: num -> bool = fun n -> Z.equal n.den z_1
  
  let is_zero: num -> bool = fun n -> (match Q.classify n with Q.ZERO -> true | _ -> false)
   
  let pow: num -> int -> num =
    fun x exp ->
      let exp' = Stdlib.abs exp in
      let n' = Z.pow x.num exp'
      and d' = Z.pow x.den exp'
      in  if exp >= 0 then Q.make n' d' else Q.make d' n'
  
  let reciprocal: num -> num =
    fun n -> Q.(n.den /// n.num)

  let zint_exactsqrt: zint -> zint option =
    fun zi -> let zr = Z.sqrt zi in
              if Z.(equal (zr*zr) zi) then Some zr else None
              
  let exactsqrt: num -> num option =
    fun n -> match zint_exactsqrt n.num, zint_exactsqrt n.den with
             | Some numr, Some denr -> Some (Q.make numr denr)
             | _                    -> None

  let gcd: num -> num -> num = (* yes it makes sense *)
    fun n m -> Q.make (Z.gcd n.num m.num) (Z.gcd n.den m.den)
end

let ( ~-: ) = Z.(~-);;
let ( /:  ) = Z.(/);;
let ( *:  ) = Z.( * );;
let ( -:  ) = Z.(-);;
let ( +:  ) = Z.(add);;
let ( =:  ) = Z.equal;;
let ( <>: ) a b = not (a =: b);;
let ( <:  ) = Z.lt;;
let ( >:  ) = Z.gt;;
let ( <=: ) = Z.leq;;
let ( >=: ) = Z.geq;;
let ( **: ) = Z.pow;;
 
let string_of_zint:   zint -> string     = Z.to_string;;
let zint_of_string:   string -> zint     = Z.of_string;;
let z_0:              zint               = Local.z_0;;
let z_1:              zint               = Local.z_1;;
let z_2:              zint               = z_1 +: z_1;;
let z_3:              zint               = z_2 +: z_1;;
let z_4:              zint               = z_2 +: z_2;;
let z_10:             zint               = Local.z_10;;

let string_of_num:       num    -> string   = Local.string_of_num;;
let num_of_string:       string -> num      = Local.num_of_string;;
let set_print_precision: num    -> unit     = Local.set_print_precision;;
let num_of_zint:         zint -> num        = Local.num_of_zint;;
let num_0:               num                = Q.zero;;
let num_1:               num                = Q.one;;
let num_2:               num                = num_of_zint z_2;;
let num_3:               num                = num_of_zint z_3;;
let num_4:               num                = num_of_zint z_4;;
let num_6:               num                = num_of_zint (Z.of_int 6);;
let num_10:              num                = num_of_zint z_10;;
let num_of_int:          int -> num         = Q.of_int;;
let int_of_num:          num -> int         = Z.to_int <.> Local.zint_of_num;;
let zint_of_num:         num -> zint        = Local.zint_of_num;;
let zint_exactsqrt:      zint -> zint option = Local.zint_exactsqrt

let ( ~-/ ) = Q.(~-);;
let ( //  ) = Q.(/);;
let ( */  ) = Q.( * );;
let ( -/  ) = Q.(-);;
let ( +/  ) = Q.(add);;
let ( =/  ) = Q.equal;;
let ( <>/ ) a b = not (a =/ b);;
let ( </  ) = Q.lt;;
let ( >/  ) = Q.gt;;
let ( <=/ ) = Q.leq;;
let ( >=/ ) = Q.geq;;
let ( **/ ) = Local.pow

let half:                num                    = num_1 // num_2;;      
let third:               num                    = num_1 // num_3;;  
let quarter:             num                    = num_1 // num_4;; 
let sixth:               num                    = num_1 // num_6;;
let threequarters:       num                    = num_3 // num_4;;

let num_30:              num                    = num_of_int 30
let num_45:              num                    = num_of_int 45
let num_60:              num                    = num_of_int 60
let num_90:              num                    = num_of_int 90
let num_180:             num                    = num_of_int 180
let num_360:             num                    = num_of_int 360 ;;

let abs:                 num -> num             = Q.abs
let pow:                 num -> int -> num      = Local.pow;;
let floor:               num -> zint            = Local.floor;;
let ceiling:             num -> zint            = Local.ceiling;;
let numden:              num -> num*num         = Local.numden;;
let div_mod:             num -> num -> zint*num = Local.div_mod;;
let div_rem:             num -> num -> zint*num = Local.div_rem;;
let num_mod:             num -> num -> num      = fun a b -> snd (div_mod a b)
let is_int:              num -> bool            = Local.is_int;;
let is_zero:             num -> bool            = Local.is_zero;;
let is_neg:              num -> bool            = fun n -> Q.sign n < 0
let reciprocal:          num -> num             = Local.reciprocal
let exactsqrt:           num -> num option      = Local.exactsqrt
let round:               num -> zint            = fun n -> floor (if Q.sign n<0 then n-/half else n+/half);;
let compare:             num -> num -> int      = Q.compare;;

let gcd:                 num -> num -> num      = Local.gcd







