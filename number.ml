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
  
  let ( // )=div
  let ( */ )=mul
  let ( -/ )=sub
  let ( +/ )=add
 
  let zero  : Z.t = Z.zero
  let one   : Z.t = Z.one
  let two   : Z.t = Z.of_string "2"
  let three : Z.t = Z.of_string "3"
  let ten   : Z.t = Z.of_string "10"
  let negone: Z.t = Z.minus_one
 
  let pow10: int -> Z.t = fun exp -> Z.pow ten exp
 
  let qpow10: int -> num = 
          fun exp -> 
              if exp>=0 then 
                 Q.make (pow10(exp)) one
              else
                 Q.make one (pow10(Pervasives.abs exp)) 

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
   
  let floor: num -> num =
      fun n ->
      let num = n.num
      and den = n.den
      in Q.make (Z.(/) num den) one

  let integer: num -> num =
      fun n ->
      let num = Z.abs n.num
      and den = Z.abs n.den
      in 
        match sign n with
        | 0    -> n
        | 1    -> Q.make (Z.div num den) one
        | _    -> Q.make (Z.div num den) negone (* sign n = -1 *)
   
  let zint_of_num: num -> zint = 
    fun n -> (integer n).num
    
  let num_of_zint: zint -> num =
    fun zi -> Q.make zi one
    
  let rem: num -> num -> num =  
    fun a -> fun b -> 
      let a = zint_of_num a in
      let b = zint_of_num b in
      num_of_zint (Z.rem a b)
      
  let numden: num -> (num*num) =
      fun n ->
      let num = Q.make n.num one
      and den = Q.make n.den one
      in (num, den)

  let divmod: num -> (num*num) =
      fun n ->
      let q, r = Z.div_rem n.num n.den
      in (Q.make q one, Q.make r one)
   
  let is_int: num -> bool = fun n -> Z.equal n.den one
   
  let pow: num -> int -> num =
    fun x exp ->
      let exp' = Pervasives.abs exp in
      let n' = Z.pow x.num exp'
      and d' = Z.pow x.den exp'
      in  if exp >= 0 then Q.make n' d' else Q.make d' n'
  
end
let num_of_string:       string -> num      = Local.num_of_string;;
let string_of_num:       num    -> string   = Local.string_of_num;;
let set_print_precision: num    -> unit     = Local.set_print_precision;;
let num_of_zint:         zint -> num        = Local.num_of_zint;;
let zero:                num                = Q.zero;;
let one:                 num                = Q.one;;
let two:                 num                = num_of_zint Local.two;;
let three:               num                = num_of_zint Local.three;;
let zzero:               zint               = Local.zero;;
let ztwo:                zint               = Local.two;;
let num_of_int:          int -> num         = Q.of_int;;

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
 
let rem:                 num -> num -> num  = Local.rem;;
let floor:               num -> num         = Local.floor;;
let numden_num:          num -> num*num     = Local.numden;;
let divmod_num:          num -> num*num     = Local.divmod;;
let integer_num:         num -> num         = Local.integer;;
let is_int:              num -> bool        = Local.is_int;;
let zint_of_num:         num -> zint        = Local.zint_of_num;;
let int_of_num:          num -> int         = Z.to_int <.> Local.zint_of_num;;







