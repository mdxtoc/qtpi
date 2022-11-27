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

(* should be called srational *)

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

(* This was once done in terms of h = sqrt (1/2) = cos (pi/4) = sin (pi/4) and 
   f = sqrt ((1+h)/2) = cos (pi/8), g = sqrt ((1-h)/2) = sin (pi/8). To get confluence
   I had to use fg  = sqrt ((1-h^2)/4) = sqrt(1/8) = h/2 and even 2fh-f = g, but I had no
   idea why. Sqrts were only of nums (rationals).
   
   Then (3.3.0) I went over to sqrt of snum and got rid of h and f and g, but I still needed
   disguised versions of the same confluences, in particular sqrt(a+b) sqrt(a-b) =
   sqrt(a^2-b^2) and (writing h for √(1/2) for the sake of clarity) 2h√(1+h) = √(1+h)+√(1-h), 
   2h√(1-h) = √(1+h)-√(1-h). Clearly the last two had to do with rotations by pi/4 and pi/8, but
   I recorded that I was too stupid to see it.
   
   (And, because I'm too stupid to remember it unless I write it down, 2h√(1+h) = √(1+h)+√(1-h)
    because multiply both sides by √(1+h), observe that 2h=√2 and you have in old money 2hff=ff+fg,
    which goes through. Phew!)
   
   Now, perhaps, an epiphany. It's all about sin and cos, and sin^2(x)=(1-cos(2x))/2, and so
   on. So this is a version which has sqrt num, cos num, sin num, and I'll see where it gets me.
   Obviously it will make great use of trigonometric identities ... watch this space.
 *)

(* The main problem was confluence, and I struggled for a while. Eventually I settled on 
   Werner's product-to-sum formulae (thanks Wikipedia, in the Trigonometric identities page) 
   -- see simplify_prod -- and keeping angles in the (0,𝜋/4] octant -- see the st_* functions
   -- and letting simplify_sum mop up.
   But the last, cruel, thing that makes it confluent is that sin(𝜋/4)=cos(𝜋/4). Oh, I hate that.
   And I bet it won't be confluent except for fractions of 𝜋/4.
   
   Modified for my purposes, and assuming (because elcompare sorts that way) that 𝜃<=𝜑, 
   Werner's identities are
   
        cos𝜃cos𝜑 = 1/2cos(𝜑-𝜃)+1/2cos(𝜃+𝜑)
        sin𝜃sin𝜑 = 1/2cos(𝜑-𝜃)-1/2cos(𝜃+𝜑)
        sin𝜃cos𝜑 = 1/2sin(𝜃+𝜑)-1/2sin(𝜑-𝜃)
        cos𝜃sin𝜑 = 1/2sin(𝜃+𝜑)+1/2sin(𝜑-𝜃)
        
 *)
 
type s_el = 
  | S_sqrt of num
  | S_trig of num * bool      (* bool is iscos; num in fractions of 𝝅: n represents n𝜋 *)
  | S_symb of s_symb                 

and s_symb = {alpha: bool; imr: bool; idsecret: symrec} 
           (* false=a / true=b,
                           false=real / true=imaginary, 
                                      shared inf.
              -- note choice of false/true alternatives because false sorts before true,
                 so a before b, real before imaginary
            *)

and symrec = {id: int; secret: (float*float)*(float*float)} 
           (* k      
                       secret amplitudes for a (re,im) and b (re,im)
                       -- note a before b, real before imaginary
                       -- never used in simplifying
                       -- total of the four must be 1.0 (do I mean that??)
            *)
             
(* S_symb is a complex unknown (with furtively a secret value, for measurement purposes only). 
    
   The secret values are _never_ used when calculating/simplifying, even if
    they are 0.0 or 1.0 (which they very very rarely might be).
 *)

and sprod = num * s_el list         (* a product*)

and snum = sprod list               (* a sum *) 

let snum_of_num n = [(n,[])]

let snum_of_zint = snum_of_num <.> num_of_zint

let sprod_neg (n,els) = ~-/n, els
 
(* this only tells you if an snum's representation starts with a minus sign *)
let printsneg_snum : snum -> bool = function
  | (n,_)::_ -> n</num_0
  | []       -> false (* because it's zero *)

let float_of_symb symb = let a,b = symb.idsecret.secret in 
                         let re,im = if symb.alpha then b else a in (* false is a *)
                         if symb.imr then im else re                (* false is re *)
  
let rec to_float snum = 
  let compute_prod (n,els) =
    Q.to_float n *. (List.fold_left ( *. ) 1.0 (List.map float_of_el els))
  in
  List.fold_left ( +. ) 0.0 (List.map compute_prod snum)

and float_of_el el = 
  match el with
  | S_sqrt x        -> Float.sqrt (Q.to_float x)
  | S_trig(x,iscos) -> (if iscos then Float.cos else Float.sin) (Float.pi *. Q.to_float x)
  | S_symb symb     -> float_of_symb symb

(* printing numbers: recursive since S_sqrt takes snum *)

let rec sum_separate = function
  | s1::s2::ss -> if Stringutils.starts_with s2 "-" then s1 ^ sum_separate (s2::ss) 
                  else s1 ^ "+" ^ sum_separate (s2::ss) 
  | [s]        -> s
  | []         -> "0" (* oh yes it can happen ... raise (Can'tHappen "sum_separate []") *)

let numopt_of_snum = function
  | [(num,[])] -> Some num
  | _          -> None
  
let string_of_symrec symrec =
  Printf.sprintf "{id=%d; secret=((%f,%f),(%f,%f))}"
                   symrec.id
                   (fst(fst symrec.secret)) (snd(fst symrec.secret))
                   (fst(snd symrec.secret)) (snd(snd symrec.secret))
                   
let dagger_string = "†"
let re_string = "𝕣"
let im_string = "𝕚"

let string_of_symb symb =
  Printf.sprintf "%s%d%s%s" 
                 (if symb.alpha then "b" else "a") 
                 symb.idsecret.id 
                 (if symb.imr then im_string else re_string)
                 (if !showabvalues then Printf.sprintf "[%f]" (float_of_symb symb) else "")

(* roots with square root symbol as unary operator, but no overline (nesting it in Unicode is a bit of a problem) *)
let rec string_of_root num =
  if num</num_0 then raise (Disaster (Printf.sprintf "string_of_root %s" (string_of_num num)))
  else
    let root n = Printf.sprintf "√(%s)" (string_of_num n) in
    let zroot zn = Printf.sprintf "√%s" (string_of_zint zn) in
    match exactsqrt num with
    | Some num' -> string_of_num num'
    | _         -> 
      if num.den=:z_1 then zroot num.num
      else match zint_exactsqrt num.num with
           | Some num' -> Printf.sprintf "%s/%s" (string_of_zint num') (zroot num.den)
           | _         ->
             match zint_exactsqrt num.den with
             | Some den' -> Printf.sprintf "%s/%s" (zroot num.num) (string_of_zint den')
             | _         -> root num
  
and string_of_trig iscos (n:num) =
  Printf.sprintf "%s(%s%s)" (if iscos then "cos" else "sin")
                            (Printf.sprintf "%s𝝅" (if n.num=:z_1 then "" else string_of_zint n.num))
                            (if n.den=:z_1 then "" 
                             else Printf.sprintf "/%s" (string_of_zint n.den)
                            )
                          
and string_of_el_struct el = 
  match el with
  | S_sqrt n         -> string_of_root n
  | S_trig (n,iscos) -> string_of_trig iscos n
  | S_symb symb      -> Printf.sprintf "{alpha=%B; imr=%B idsecret=%s}" 
                             symb.alpha symb.imr (string_of_symrec symb.idsecret)

and string_of_els_struct els = bracketed_string_of_list string_of_el_struct els

and string_of_prod_struct prod = bracketed_string_of_pair string_of_num string_of_els_struct prod

and string_of_snum_struct snum = bracketed_string_of_list string_of_prod_struct snum

and string_of_snums_struct snums = bracketed_string_of_list string_of_snum_struct snums

and so_el symbf e = 
  match !fancynum with
  | RawNum -> string_of_el_struct e
  | _      ->
      match e with
      | S_sqrt n         -> string_of_root n
      | S_trig (n,iscos) -> string_of_trig iscos n    (* one day this will recognise values of n *)
      | S_symb symb      -> symbf symb
  
and string_of_el el = so_el string_of_symb el

and so_els symbf es = String.concat "" (List.map (so_el symbf) es)

and string_of_els es = 
  (match !fancynum with
   | RawNum -> string_of_els_struct
   | _      -> so_els string_of_symb 
  ) es

(* I want to get this right once, so I can deal with real and imaginary products.
   si is "" or "i",
   
   And oh what a mess I made of it. But now, I hope, it's a bit better ...
 *)  

and so_prodi si symbf (n,els) = 
  match !fancynum with
  | RawNum        -> si ^ "*" ^ string_of_prod_struct (n,els)
  | FractionalNum ->
      if n</num_0         then "-" ^ so_prodi si symbf (~-/n,els)   else
      if n=/num_0         then "0" (* shouldn't happen *)           else
      let rcstring () =
        let rec rc_els bra = function
          | S_sqrt n :: els          -> let s = string_of_root n in
                                        (if bra then "(" ^ s ^ ")" else s) ^ rc_els true els
          | S_trig (n, iscos) :: els -> string_of_trig iscos n ^ rc_els true els
          | S_symb s :: els          -> symbf s ^ rc_els true els
          | []                       -> ""
        in
        if n=/num_1 && els<>[] then rc_els false els
                               else string_of_num n ^ rc_els true els 
      in
      let s = if not !rootcombine then rcstring () 
              else (let rec roots accum els =
                      match els with
                      | S_sqrt n :: els'          -> roots (n*/accum) els'
                      | S_trig (n,_) :: els'         
                          when n=quarter          -> (* sin 𝝅/4 = cos 𝝅/4 = 1/√2 *)
                                                     roots (half*/accum) els' 
                      | S_trig (n,true) :: els' 
                          when n=sixth            -> (* cos 𝝅/6 = √3/2 *)
                                                     roots (threequarters*/accum) els'
                      | _                         -> accum, els
                    in
                    let sq, els = roots (n*/n) els in
                    if els=[]           then string_of_root sq                                           else 
                    if sq=/num_1        then so_els symbf els                                            else
                    if sq.den=:z_1      then string_of_root sq ^ so_els symbf els                        else
                    if sq.num=:z_1      then so_els symbf els ^ "/" ^ string_of_root (reciprocal sq)     else
                                             "(" ^ string_of_root sq ^ ")" ^ so_els symbf els
                   )
      in
      if si="" then s else
      if s="1" then si else
       let c = Stringutils.last s in
       if c = ')' || ('0'<=c && c<='9') then s ^ si else
       let c' = Stringutils.first s in
       if 'a'=c' || 'b'=c' then si ^ "*" ^ s else
       si ^ "*(" ^ s ^ ")"

and string_of_sprod p = so_prodi "" string_of_symb p 

and fracparts (s:snum) : string list = List.map string_of_sprod s

and string_of_snum (s:snum) = 
  match !fancynum with
  | RawNum        -> string_of_snum_struct s
  | FractionalNum -> sum_separate (fracparts s)

and string_of_snums snums = bracketed_string_of_list string_of_snum snums

(* normalising S_trig *)
let st_neg = function
  | None         -> None
  | Some (n,els) -> Some (~-/n,els)

(* result is (0,𝜋/4] -- doesn't include 0, includes 𝜋/4 *)
(* input in [0,𝜋/2] -- closed, includes both endpoints *)
let st_half iscos n = 
        (*  if n>/quarter 
            then (if n=/half 
                    then if iscos then None else Some (num_1,[])            (* because cos(𝜋/2)=0, sin(𝜋/2)=1 *)
                    else Some (num_1, [S_trig (half-/n,not iscos)])         (* because sin(𝜋/2-n)=cos n and cos(𝜋/2-n=sin n) *)
                 )
            else (if n=/quarter 
                    then Some (num_1, [S_trig (n, true)])       (* because sin(𝜋/4)=cos(𝜋/4) *) 
                    else if n=num_0 then if iscos then Some (num_1,[]) else None    (* because cos 0=1, sin 0=0 *)
                                    else Some (num_1, [S_trig (n, iscos)])
                 )       
        *)
  (* this has got a bit worse because of 𝝅/3 and 𝝅/6 *)
  match n=/num_0, n=/half, n=/third, n=/sixth, iscos with
  | true, _   , _   , _   , false           (* sin 0 = 0 *)   
  | _   , true, _   , _   , true            (* cos 𝜋/2 = 0 *)
                      -> None
  | true, _   , _   , _   , true            (* cos 0 = 1 *)
  | _   , true, _   , _   , false           (* sin 𝜋/2 = 1 *)
                      -> Some (num_1,[])
  | _   , _   , true, _   , true            (* cos 𝝅/3 = 1/2 *)
  | _   , _   , _   , true, false           (* sin 𝝅/6 = 1/2 *)
                      -> Some (half,[])
  | _                 -> Some (num_1,[match n>/quarter, n=/quarter with
                                      | true, _    -> S_trig (half-/n,not iscos)    (* because sin(𝜋/2-n)=cos n and cos(𝜋/2-n=sin n) *)
                                      | _   , true -> S_trig (n, true)              (* because sin(𝜋/4)=cos(𝜋/4) *) 
                                      | _          -> S_trig (n,iscos)
                                     ])

(* input in [0,𝜋] -- closed, includes both endpoints *)
let st_1 iscos n =
  match n>/half, iscos with
  | true , true  -> st_neg (st_half iscos (num_1-/n)) 
  | true , false -> st_half iscos (num_1-/n)
  | _            -> st_half iscos n

(* input in [0,2𝜋] -- closed, includes both endpoints *)
let st_2 iscos n = 
  match n>/num_1, iscos with
  | true, true  -> st_1 iscos (num_2-/n)
  | true, false -> st_neg (st_1 iscos (num_2-/n))
  | _           -> st_1 iscos n

let st_norm st_f iscos n = 
  match st_f iscos n with
  | Some sprod -> [sprod]
  | None       -> []
 
(* this is slow: don't use in simplification. But note: if it gives you an S_trig (x,_)
   then x is in the interval (0,quarter]
 *)
let snum_trig iscos n = st_norm st_2 iscos (num_mod n num_2)

let sprod_1 :sprod = (num_1,[])

(* cos 𝝅/4 = 1/√2 *) 
let s_el_h  :s_el = S_trig (quarter, true) (* ok to use S_trig *)

let sprod_h :sprod = (num_1,[s_el_h])

(* cos 𝝅/6 = √3/2, so 2/3 (cos 𝝅/6) = 1/√3 *)
let sprod_t :sprod = (num_2//num_3, [S_trig (sixth, true)]) (* ok to use S_trig *)

let snum_0 :snum = []

let snum_1 :snum = [sprod_1]

let snum_h :snum = [sprod_h]
let snum_t :snum = [sprod_t]

let eighth = quarter // num_2

let snum_sqrt (n:num) = match zint_exactsqrt n.num, zint_exactsqrt n.den with
                        | Some num, Some den -> [(Q.make num den, [])]
                        | Some num, None     -> [(Q.make num z_1 ,[S_sqrt(Q.make z_1 n.den)])] 
                        | None    , Some den -> [(Q.make z_1 den, [S_sqrt(Q.make n.num z_1)])] 
                        | None    , None     -> [(num_1         , [S_sqrt n])]

(* .. not really needed yet ..

   let sprod_third   = (third, [])

   let snum_third = [sprod_third]

   let snum_t = [(num_1, [S_sqrt snum_third])]
 *)
 
let snum_symb symb :snum = [(num_1, [S_symb symb])]

(* The normal form -- now the snum type -- is a sum of products. 
 * Sign is now naturally included in the num element of a product.
 * I would like to sort snums so that the same el lists are adjacent but otherwise 
 * largest num first, as in the prodcompare function that used to be in simplify_sum.
 * Otherwise sqrts before cos before sin before symbs, and the natural ordering on symbs (because alpha
 * and imr fields are designed for it).
 *)
 
let (<??>) : int -> ('a -> int) -> ('a -> int)  =
             fun i f -> if i=0 then f else (fun _ -> i)

let revcompare cf a b = ~- (cf a b)

let rec listcompare : ('a -> 'a -> int) -> 'a list -> 'a list -> int =
  fun cf xs ys ->
    match xs, ys with
    | x::xs, y::ys -> (cf x y <??> listcompare cf xs) ys
    | []     , []      -> 0
    | []     , _       -> ~-1
    | _      , []      -> 1
;;

let rec snumcompare : snum -> snum -> int = 
  fun n1 n2 -> listcompare prodcompare n1 n2

and elscompare : s_el list -> s_el list -> int = 
  fun els1 els2 -> listcompare elcompare els1 els2

and prodcompare : sprod -> sprod -> int =
  fun (n1,els1) (n2,els2) -> (elscompare els1 els2 <??> ((~-) <.> Stdlib.compare n1)) n2 
  
(* sqrt, trig, symb -- but trig is sorted on (n, iscos) -- so a definition of the type does it *)
(* but actually Stdlib.compare doesn't do rationals properly, so it doesn't quite *)
(* but the only place we really need the order is in simplify_sum ... *)
and elcompare : s_el -> s_el -> int = 
  fun el1 el2 ->
    match el1, el2 with
    | S_trig(n1,ic1), S_trig(n2,ic2) -> (Number.compare n1 n2 <??> Stdlib.compare ic1) ic2
    | _                              -> Stdlib.compare el1 el2
           
(* *********************** symbolic arithmetic ************************************ *)

let make_snum_h k = 
  if k<0 then (* look out for div, mod going towards 0 *)
    let n = Number.pow num_2 (((~-k)+1)/2) in
    let els = if (~-k) mod 2 = 1 then [s_el_h] else [] in
    [(n,els)]
  else
    let n = Number.pow half (k/2) in
    let els = if k mod 2 = 1 then [s_el_h] else [] in
    [(n,els)]

let rmult_num sn n =
  if n=/num_0 then snum_0  else 
  if n=/num_1 then sn      else
  List.map (fun (m,els) -> n*/m,els) sn
  
let rmult_zint sn zi = rmult_num sn (num_of_zint zi)

let rec rneg s =
  let r = List.map sprod_neg s in
  if !verbose_simplify then
    Printf.printf "rneg (%s) -> %s\n" (string_of_snum s) (string_of_snum r);
  r
    
and rprod s1 s2 :snum =
  let r = match s1, s2 with
          | [(n1,[])], _         -> rmult_num s2 n1
          | _        , [(n2,[])] -> rmult_num s1 n2
          | _                    ->
              let rp (n1,els1) (n2,els2) = simplify_prod (n1*/n2, els1@els2) in (* simplify_prod does the sorting *)
              simplify_sum (List.fold_left 
                              (fun sum prod1 -> 
                                 List.fold_left (fun sum prod2 -> (rp prod1 prod2) @ sum) sum s2 (* yes, append (sigh) *)
                              )
                              []
                              s1
                           )
  in
  if !verbose_simplify then
    Printf.printf "rprod (%s) (%s) -> %s\n" (string_of_snum s1) (string_of_snum s2) (string_of_snum r);
  r
  
and simplify_prod (n,els as prod) :snum = (* We deal with sqrt^2, trig*trig. *)
  (* In the past it was possible to imagine that we might get more than one instance of the 'premult'
     behaviour from a prod, and that once we had gone once round the list of elements and made some
     changes, we should go round again, and so on until it all settled down. That's still believable
     in simplify_sum, but in the new dispensation we have at most two trigs in a prod, as a result of
     a multiplication, and simplification _always_ reduces that to one. So now we don't go to the end 
     of a prod to look for stuff, and we don't look any further after we've failed to find a trig::trig::ss.
     And we don't use rmult and rprod to force going round again. It is to hoped that this will
     speed up simplification (which slowed by a factor of 3 in the Ekert example when we went all-trig.)
     RB 2022/10/02
     Oh dear. If anything it made things minutely slower .... what to do? ...
     But oh dear oh dear oh dear. The Ekert simplification, in the old version, was using a hermititian matrix
     rather than a rotation matrix. So Rz (which is what it was called) was such that Rz*Rz = I, and it was 
     not doing 𝝅/8, 2𝝅/8 and 3𝝅/8 rotations. When I corrected the rotations, it was slower than the all-trig
     mechanism. So hurrah! I think I've reached the end of the symbolic-calculator development. 
     RB 2022/10/25
     Except I just had to add the stuff for cos(𝝅/3) = sin(𝝅/6) = 1/2. 
     RB 2022/11/27
   *)
  let r = let rec sp els n ss = 
            if !verbose_simplify then 
              Printf.printf "sp %s %s %s\n" (string_of_els els) (string_of_num n) (string_of_els ss);
            let premult s n ss = 
              (* let popt, n, ss = sp els n ss in
                   (match popt with 
                    | Some pre_p -> Some (rprod pre_p s)
                    | None       -> Some s
                   ), n, ss
               *)
              Some s, n, els, ss
            in
            (* not used at present, because of optimisation below
               let wtrig w iscos theta tail = 
                 match st_half iscos theta with
                 | Some (n,[el]) -> (n*/w,Some el) :: tail
                 | Some (n,[])   -> (n*/w,None) :: tail
                 | _             -> tail
               in
             *)
            match ss with
            | S_sqrt a      :: S_sqrt b :: ss                       (* √a*√a = a *)
              when a=b                   -> sp els (n*/a) ss
            | S_sqrt a as s :: ss        -> sp (s::els) n ss
            | S_trig (a,ac) :: S_trig (b,bc) :: ss                  (* use the Werner identities. Note that b>=a and that a, b are in (0,𝝅/4] *)
                                         -> let sum = b+/a in
                                            let diff = b-/a in
                                            let pm sumw sumcos diffw diffcos = (* trying to speed this up *)
                                              let sumr = 
                                                if sum>/quarter then if sum=/half             then if sumcos then []                (* cos(𝝅/2) = 0 *)
                                                                                                             else [(sumw,None)]     (* sin(𝝅/2) = 1 *)
                                                                     else 
                                                                     if sum=/third && sumcos then [(sumw*/half,None)]               (* cos(𝝅/3) = 1/2 *)
                                                                                             else [(sumw, Some (S_trig (half-/sum, not sumcos)))]
                                                                else if sum=/quarter then [(sumw, Some (S_trig (sum,true)))]
                                                                                     else [(sumw, Some (S_trig (sum, sumcos)))]
                                              in
                                              let r =
                                                if diff=/num_0 then if diffcos then (diffw,None)::sumr                              (* cos 0 = 1 *)
                                                                               else sumr                                            (* sin 0 = 0 *)
                                                else 
                                                if diff=/sixth && not diffcos  then (diffw*/half,None)::sumr                        (* sin(𝝅/6) = 1/2 *)
                                                                               else (diffw, Some (S_trig (diff,diffcos))) :: sumr
                                              in
                                              if !verbose || !verbose_simplify then
                                                (let foodle =bracketed_string_of_list (bracketed_string_of_pair string_of_num (string_of_option string_of_el)) r in
                                                 Printf.printf "%s%s a+b=%s pm=%s\n" (string_of_el (S_trig (a,ac))) (string_of_el (S_trig (b,bc))) (string_of_num (b+/a)) foodle
                                                );
                                              r
                                            in
                                            premult (match ac, bc with
                                                     | true , true  (* cos𝜃cos𝜑 = 1/2cos(𝜑-𝜃)+1/2cos(𝜃+𝜑) *)
                                                                    -> pm half      true  half      true
                                                     | false, false (* sin𝜃sin𝜑 = 1/2cos(𝜑-𝜃)-1/2cos(𝜃+𝜑) *)
                                                                    -> pm (~-/half) true  half      true
                                                     | false, true  (* sin𝜃cos𝜑 = 1/2sin(𝜃+𝜑)-1/2sin(𝜑-𝜃) *)
                                                                    -> pm half      false (~-/half) false
                                                     | true , false (* cos𝜃sin𝜑 = 1/2sin(𝜃+𝜑)+1/2sin(𝜑-𝜃) *)
                                                                    -> pm half      false half      false
                                                    ) n ss
            | _                          -> None, n, els, ss
          in
          let popt, n, els, ss = sp [] n (List.sort elcompare els) in (* do we really need this sort? We could use merge in rprod/rmult *)
          match popt with 
          | Some pre_p -> List.sort prodcompare (List.map (function (n', Some el) -> (n*/n', Listutils.prepend els (el::ss))
                                                                |   (n', None   ) -> (n*/n', Listutils.prepend els ss)
                                                          )
                                                          pre_p
                                                )
          | None       -> [(n, Listutils.prepend els ss)]
  in
  if !verbose_simplify then
    Printf.printf "simplify_prod %s -> %s\n" (string_of_sprod prod) (string_of_snum r);
  r

and rsum s1 s2 = 
  let r = simplify_sum (s1 @ s2) in
  if !verbose_simplify then
    Printf.printf "rsum (%s) (%s) -> %s\n" (string_of_snum s1) (string_of_snum s2) (string_of_snum r);
  r

and sflatten ss = (* flatten a list of sums *)
     let r = List.concat ss in
     if !verbose_simplify then
       Printf.printf "sflatten %s -> %s\n" 
                     (bracketed_string_of_list string_of_snum ss) 
                     (string_of_snum r);
     r

(*
   and ihs i ss = if i=0 then ss else S_h i::ss
 *)

and simplify_sum ps = 
  let r = let multiple (n,els:sprod) rest = (* looking for nX+mX+... -- we sum the num parts *)
            let r = (match takedropwhile (fun (_,els') -> els=els') rest with
                     | [] , _   -> n, rest
                     | ps, rest -> List.fold_left (fun sum (m,_) -> m+/sum) n ps, rest
                    )
            in
            if !verbose_simplify then
              Printf.printf "multiple (%s) %s -> %s\n" (string_of_sprod (n,els))  
                                                       (bracketed_string_of_list string_of_sprod rest)
                                                       (string_of_pair string_of_num (bracketed_string_of_list string_of_sprod) "," r);
            r
          in
          let rec a2b2 p ps = (* looking for X*aa!Y+X*bb!Y to replace with XY. Sorting doesn't always make aa! and bb! next to each other in ps *)
                              (* and now we have real and imaginary parts ... *)
            let n,els = p in
            let rec find pres els =
              match els with 
              | S_symb ({alpha=false; imr=false; idsecret={id=q1}} as symb1) :: 
                S_symb ({alpha=false; imr=false; idsecret={id=q2}} as symb2) :: els (* we have found a.re*a.re *)
                          when q1=q2 
                          -> 
                  let remake post = n, prepend pres post in
                  let fail () = find (S_symb symb2::S_symb symb1::pres) els in
                  let p' = remake (S_symb {symb1 with alpha=true} :: S_symb {symb2 with alpha=true} :: els) in
                  if !verbose_simplify then 
                    Printf.printf "a2b2.find looking for %s (b.re*b.re) in %s\n" (string_of_sprod p') (string_of_snum ps);
                  if List.exists ((=) p') ps 
                  then (
                    (* we have also found b.re*b.re *)
                    let ps' = Listutils.remove p' ps in
                    (* search for a.im*a.im and b.im*b.im *)
                    let pa' = remake (S_symb {symb1 with imr=true} :: S_symb {symb2 with imr=true} :: els) in
                    if !verbose_simplify then 
                      Printf.printf "a2b2.find looking for %s (a.im*a.im) in %s\n" (string_of_sprod pa') (string_of_snum ps);
                    if List.exists ((=) pa') ps' then (
                      let pb' = remake (S_symb {symb1 with alpha=true; imr=true} :: S_symb {symb2 with alpha=true; imr=true} :: els) in
                      if !verbose_simplify then 
                        Printf.printf "a2b2.find looking for %s (b.im*b.im) in %s\n" (string_of_sprod pb') (string_of_snum ps);
                      if List.exists ((=) pb') ps' then (
                        if !verbose_simplify then 
                          Printf.printf "a2b2.find success!\n";
                        Some (remake els, Listutils.remove pb' (Listutils.remove pa' ps'))
                      )
                      else fail ()
                    )
                    else fail ()
                  )
                  else fail ()
              | el :: els  -> find (el::pres) els
              | _          -> None
            in
            let r = find [] els in (* could recurse, but we're just looking in one spot *)
            if !verbose_simplify then
              Printf.printf "a2b2 (%s) -> %s\n" (string_of_snum ps) 
                                                (string_of_option (bracketed_string_of_pair string_of_sprod string_of_snum) r);
            r
          in
          let rec sps again (r:sprod list) (ps:sprod list) =
            if !verbose_simplify then 
              Printf.printf "sps %B %s %s\n" again (string_of_snum r) (string_of_snum ps);
            match ps with
            | (n1,es1) :: (n2,es2) :: ps 
              when es1=es2                         -> let n', ps' = multiple (n1+/n2,es1) ps in
                                                      if n'=/num_0 then sps true r ps' else sps true ((n',es1)::r) ps'
             
            (* we try a^2+b^2=1 *) 
            | p                  :: ps            -> (match a2b2 p ps with
                                                      | Some (p',ps') -> sps true (p'::r) ps'
                                                      | None          -> sps again (p::r) ps
                                                     )
            | []                                  -> if again then doit r else List.sort prodcompare r
          and doit ps = sps false [] (List.sort prodcompare ps)
          in
          doit ps
  in
  if !verbose_simplify then
    Printf.printf "simplify_sum (%s) -> %s\n" (string_of_snum ps) (string_of_snum r);
  r

(* given the wrong numbers, this will generate lots of strange S_sqrt entries ... 
   so be careful
 *)
let reciprocal_sqrt (n:num) = if n=/num_2 then snum_h else 
                              if n=/num_3 then snum_t else
                                               [(reciprocal n, [S_sqrt n])] (* don't introduce √ if possible *)

let rdiv_sqrt sn n = 
  rprod (reciprocal_sqrt n) sn

  
(******** snum arithmetic is where all the action is. So we memoise sum and prod, carefully *********)

module SnumH = struct type t = snum 
                      let equal = (=)
                      let hash = Hashtbl.hash
                      let to_string = string_of_snum
               end
module SnumHash = MyHash.Make (SnumH)

let memofunProb ident f = 
  let table = SnumHash.create 100 in
  SnumHash.memofun ident table (fun s -> let r = f s in
                                         if !verbose || !verbose_simplify || !verbose_memo then 
                                            Printf.printf "memofun %s (%s) -> %s\n" ident (string_of_snum s) (string_of_snum r); 
                                         r
                               )

let memofun2Prob ident f = 
  let t1 = SnumHash.create 100 in
  SnumHash.memofun (ident ^ " 1") t1 
    (fun s1 -> let t2 = SnumHash.create 100 in
               SnumHash.memofun (ident ^ " 2") t2 
                 (fun s2 -> let r = f s1 s2 in
                            if !verbose || !verbose_simplify || !verbose_memo 
                            then Printf.printf "memofun2 %s (%s) (%s) -> %s\n" 
                                               ident 
                                               (string_of_snum s1) 
                                               (string_of_snum s2)
                                               (string_of_snum r); 
                            r
                 )
    )

let raw_rprod = rprod
let memo_rprod = memofun2Prob "rprod" rprod (* doesn't save more than a tiny bit *)

let rec rprod s1 s2 =
  if !Settings.memoise then
    match s1, s2 with
    (* we do simple numbers ourselves *)
    | []          , _
    | _           , []           -> []   
    | [(n1,[])]   , _            -> rmult_num s2 n1
    | _           , [(n2,[])]    -> rmult_num s1 n2
    (* we memoise everything else *)
    | _                          -> memo_rprod s1 s2
  else
    raw_rprod s1 s2

let raw_rsum = rsum
let memo_rsum = rsum (* memofun2Prob rsum "rsum" *)

let rec rsum s1 s2 =
  if !Settings.memoise then
    match s1, s2 with
    (* we do 0 ourselves *)
    | []      , _       -> s2
    | _       , []      -> s1
   (* (* we memoise sum *)
      | S_sum  _ , _
      | _       , S_sum  _ -> memo_rsum s1 s2
      (* everything else is raw *)
      | _                 -> raw_rsum s1 s2 
    *)
    | _                 -> memo_rsum s1 s2
  else
    memo_rsum s1 s2

(* memoising simplify_sum slows things down, at least in Grover ... *)
let raw_simplify_sum = simplify_sum  
let memo_simplify_sum = memofunProb "simplify_sum" simplify_sum

let memoise_simplify_sum = false

let simplify_sum =
  if !Settings.memoise && memoise_simplify_sum then memo_simplify_sum
  else raw_simplify_sum 

(* this is for division that sometimes works *)
let rdiv r1 r2 =   
  let bad () = raise (Disaster (Printf.sprintf "rdiv cannot divide %s by %s" (string_of_snum r1) (string_of_snum r2))) in
  if r2=snum_0 then bad () else
  if r1=r2     then snum_1 else
    match r2 with
    | [n2,els2] -> let el_div (n1,els1) el =
                     if List.mem el els1 then n1, Listutils.remove el els1 else
                       match el with
                       | S_sqrt n         -> Q.div n1 n, el::els1
                       | S_trig (n,_) 
                           when n=quarter -> Q.div n1 half, el::els1
                       | _                -> bad ()
                   in
                   let sn_div (n1,els1) = List.fold_left el_div (Q.div n1 n2, els1) els2 in
                   simplify_sum (List.map sn_div r1)
    | _         -> bad () (* can't divide by a sum *)
    
(* *********************** complex arith in terms of reals ************************************ *)

type csnum = C of snum*snum (* complex x + iy *)

(* this doesn't really work: only useful if thinking about printed form of a number *)
let printsneg_csnum = function
  | C([], y) -> printsneg_snum y
  | C(x , _) -> printsneg_snum x
  
let so_im y = (* a list of strings: ok if y is zero *) 
  match y with
  | []                 -> []
  | [p]                -> [so_prodi "i" string_of_symb p]
  | _                  -> ["i*(" ^ string_of_snum y ^ ")"]

let so_csnumb bracket (C (x,y)) =
  match !fancynum with
  | RawNum        -> "C(" ^ string_of_snum x ^ "," ^ string_of_snum y ^ ")" 
  | FractionalNum ->
      let fracparts_c (xs,ys) =
        let rec parts ypres ss (xs,ys) = 
          match xs,ys with 
          | _              , [] 
          | []             , _  -> 
              let ypart = match ypres, ys with
                          | []     , _  -> so_im ys
                          | [(f,p)], [] -> [so_prodi "i" f p]
                          | _           -> ["i*(" ^ sum_separate (Listutils.prepend (List.map (fun (f,p) -> so_prodi "" f p) ypres) 
                                                                                    (List.map string_of_sprod ys)
                                                                 )
                                                  ^ ")"]
              in
              Listutils.prepend ss (fracparts xs @ ypart)
          | (n,ps as x)::xs, _  -> 
              let default () = parts ypres (string_of_sprod x :: ss) (xs,ys) in
              let rec treatable imropt ps = (* result Some imr means ps contains just one variable, with re/im imr;
                                                      None     means otherwise.
                                             *)
                match ps with
                | []    -> imropt
                | p::ps -> (match imropt, p with
                            | Some imr, S_symb s -> None
                            | None    , S_symb s -> treatable (Some s.imr) ps
                            | _                  -> treatable imropt ps
                           )
              in
              (* try to deal with the case where there's one variable whose real and imaginary parts are on opposite sides.
                 It would be much harder to deal with the case where there are multiple variables, and I haven't tried.
               *)
              match !showunknownparts, treatable None ps with
              | true, _        
              | _   , None     -> default ()
              | _   , Some imr -> 
                  let rec findsame ypres ys = (* result Some(eq,ys') means we found in ys an element y' same as x, with sign equal or opposite, 
                                                                           and with opposite imr, and ys' is ys with y' extracted;
                                                        None         means we couldn't do that
                                               *)
                    let rec sameps ps ps' = (* is ps the same as ps', with opposite imr? *)
                      match ps, ps' with
                      | p::ps, p'::ps' -> (match p, p' with
                                           | S_symb s, S_symb s' -> s={s' with imr=not s'.imr}
                                           | _                   -> p=p'
                                          ) && sameps ps ps'
                      | []   , []      -> true
                      | _              -> false
                    in
                    match ys with
                    | []                -> None
                    | (n',ps' as y)::ys -> let again () = findsame (y::ypres) ys in
                                           if sameps ps ps' then
                                             if n=/n'      then Some (true , Listutils.prepend ypres ys) else
                                             if n=/(~-/n') then Some (false, Listutils.prepend ypres ys) else 
                                                                again ()
                                           else again ()
                  in
                  if !complexcombine then
                    match findsame [] ys with
                    | Some (sign, ys) -> let float_of_symb s = let a,b = s.idsecret.secret in
                                                               (fun (re,im) -> Float.sqrt (re*.re+.im*.im))
                                                                  (if s.alpha then a else b)
                                         in
                                         let symbf s =   Printf.sprintf "%s%d%s%s" 
                                                           (if s.alpha then "b" else "a") 
                                                           s.idsecret.id 
                                                           (if sign<>s.imr then "" else dagger_string)
                                                           (if !showabvalues then Printf.sprintf "[%f]" (float_of_symb s) else "")
                                         in
                                         if imr then parts ((symbf, (~-/n,ps)):: ypres) ss                          (xs,ys)
                                                else parts ypres                        (so_prodi "" symbf x :: ss) (xs,ys)
                    | None            -> default ()
                  else default ()
        in
        parts [] [] (x,y) 
        (* double printing to see what it was we were simplifying: commented out because the above seems to work ...
           @ (showunknownparts := not !showunknownparts; 
              let ss = parts [] [] (x,y) in 
              showunknownparts := not !showunknownparts; 
              ("[" :: ss) @ ["]"])
             )
         *)
      in
      let ss = match x,y with
               | [] , []            -> ["0"]
               | _  , []            -> fracparts x
               | [] , _             -> so_im y
               | _  , _             -> fracparts_c (x,y)
      in
      match bracket, ss with
      | false, _   -> sum_separate ss
      | _    , [s] -> s
      | _          -> "(" ^ sum_separate ss ^ ")"

let string_of_csnum = so_csnumb false

let csnum_of_snum s = C (s, snum_0)

let c_0 = csnum_of_snum snum_0
let c_1 = csnum_of_snum (snum_1)
let c_h = csnum_of_snum (snum_h)
let c_reciprocal_h = csnum_of_snum (reciprocal_sqrt half)

let c_i = C (snum_0, snum_1)

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
  if c1=c_0 || c2=c_0 then c_0  else
  if c1=c_1           then c2   else
  if c2=c_1           then c1   else
  match x1,y1, x2,y2 with
  | [], [] , _ , _    
  | _ , _  , [], [] -> c_0
  | _ , [] , _ , [] -> intern (C (rprod x1 x2    , []))         (* real    * real    *)
  | _ , [] , _ , _  -> intern (C (rprod x1 x2, rprod x1 y2))    (* real    * complex *)
  | _ , _  , _ , [] -> intern (C (rprod x1 x2, rprod y1 x2))    (* complex * real    *)
  | _               -> intern (C (rsum (rprod x1 x2) (rneg (rprod y1 y2)), rsum (rprod x1 y2) (rprod y1 x2)))

let cprod_r c1 r = cprod c1 (C (r,[]))

let csum (C (x1,y1) as c1) (C (x2,y2) as c2) = 
  match x1,y1, x2,y2 with
  | [] , [] , _  , _    -> c2 
  | _  , _  , [] , []   -> c1
  | _                   -> intern (C (rsum x1 x2, rsum y1 y2))

let simplify_csum = function
  | [] -> c_0
  | cs -> let reals, ims = List.split (List.map (fun (C (x,y)) -> x,y) cs) in
          C (simplify_sum (sflatten reals), simplify_sum (sflatten ims))  

let cdiff c1 c2 = csum c1 (cneg c2)

let cconj (C(x,y)) = intern (C (x, rneg y))

let absq  (C(x,y)) = rsum (rprod x x) (rprod y y)

(* we can't really divide, but we try. And so far only used in printing, so no intern *)

let cdiv (C (x1,y1) as c1) (C (x2,y2) as c2) = 
  let bad () = 
    raise (Disaster (Printf.sprintf "cdiv cannot divide %s by %s" (string_of_csnum c1) (string_of_csnum c2)))
  in
  if c2=c_0 then bad () else
  if c1=c2  then c_1 
  else 
    match x1  , y1  , x2  , y2 with  
    |     []  , []  , _   , _    -> c_0
    |     _   , _   , _::_, []   -> C (rdiv x1 x2, rdiv y1 x2)
    |     []  , _::_, []  , _::_ -> C ([], rdiv y1 y2)
    |     _                      -> bad ()

let cdiv_r   c r                  = cdiv c (C(r,[]))

let cmult_zint (C(x,y)) zi        = intern (C (rmult_zint x zi, rmult_zint y zi))

(* we no longer memoise any complex arithmetic functions ...

    module OrderedC = struct type t = csnum 
                             let compare = Stdlib.compare
                             let to_string = string_of_csnum
                      end
    module CMap = MyMap.Make (OrderedC)
    let memofunC ident f s = CMap.memofun ident id (fun c -> if !verbose || !verbose_qcalc || verbose_memo then Printf.printf "%s (%s)\n" s (string_of_csnum c); f c)

    module OrderedC2 = struct type t = csnum*csnum 
                             let compare = Stdlib.compare
                             let to_string = bracketed_string_of_pair string_of_csnum string_of_csnum
                      end
    module C2Map = MyMap.Make (OrderedC2)
    let memofunC2 ident f s = 
      curry2 (C2Map.memofun ident id (uncurry2 (fun c1 c2 -> if !verbose || !verbose_qcalc then 
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
    let memofunCP ident f s = 
      curry2 (CPMap.memofun ident id (uncurry2 (fun c s -> if !verbose || !verbose_qcalc then 
                                                       Printf.printf "%s (%s) (%s)\n" 
                                                                     s (string_of_csnum c) (string_of_snum s);
                                                     f c s
                                        )
                               )
             )

    let mcprod = memofunC2 "cprod" cprod
    let cprod (C (x1,y1) as c1) (C (x2,y2) as c2) = 
      match x1,y1, x2,y2 with
      | S_0          , S_0, _            , _    
      | _            , _  , S_0          , S_0       -> c_0
      | S_h 0        , S_0, _            , _         -> c2  
      | _            , _  , S_h 0        , S_0       -> c1
      | S_neg (S_h 0), S_0, _            , _         -> cneg c2  
      | _            , _  , S_neg (S_h 0), S_0       -> cneg c1
      | _                                            -> mcprod c1 c2
  
    let mcsum = memofunC2 "csum" csum
    let csum  (C (x1,y1) as c1) (C (x2,y2) as c2) = 
      match x1,y1, x2,y2 with
      | S_0, S_0, _  , _    -> c2 
      | _  , _  , S_0, S_0  -> c1
      | _                   -> mcsum c1 c2
  
    (* let cneg = memofunC "cneg" cneg -- possibly not worth it *)
    (* let cconj = memofunC "cconj" cconj -- not worth it *)

    (* absq is used a lot in measurement: perhaps worth memoising. Or rather perhaps not,
       if rsum and rmult are memoised.
     *)
    let absq x = (if !Settings.memoise then memofunC "absq" absq else absq) x

    (* we can't really divide
        let c_r_div = memofunCP "c_r_div" c_r_div
        let c_r_div_h = memofunC "c_r_div_h" c_r_div_h
     *)
 *)

