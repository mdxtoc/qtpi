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

(* h = sqrt (1/2) = cos (pi/4) = sin (pi/4); useful for rotation pi/4, or 45 degrees;
   f = sqrt ((1+h)/2) = cos (pi/8); useful for rotation pi/8 or 22.5 degrees;
   g = sqrt ((1-h)/2) = sin (pi/8); the partner of f;
   
   Note h^2 = 1/2; 
        f^2 = (1+h)/2 = 1/2+h/2;
        g^2 = (1-h)/2 = 1/2-h/2;
        fg  = sqrt ((1-h^2)/4) = sqrt(1/8) = h/2  
        
        f/h-f = g
        gh^3  = gfg = fg^2 -- not used
        gh = f(1-h)
    
    We also used to have
        2fh-f = g
        -- which it is possible to justify ... but now, with the simpler formulation
           of snum_f and snum_g (see below), and still for simplicity writing h for √(1/2), we have
        2h√(1+h) = √(1+h)+√(1-h)
        2h√(1-h) = √(1+h)-√(1-h)
        -- all something to do with pi/4 and pi/8 rotations, I suspect, but I'm too stupid to see it.
 *)

(* for a long time this was done in terms of h = sqrt (1/2). But that's embarrassing now.
   So: something more general: numbers, square roots, symbols, sums and prods. 
   But sorting is a problem, because I want to sort snums largest number first, and
   S_sqrt contains an snum. That means complicated comparison functions. Hmm.
 *)
type s_el = 
  | S_sqrt of snum
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
             
and sprod = num * s_el list         (* a product*)

and snum = sprod list               (* a sum *) 

(* S_symb is an unknown (with furtively a secret value). 
   S_symb is a complex number. 
    
    The secret values are used when measuring, to compute the value of a formula
    involving the symbol. They are _never_ used when calculating/simplifying, even if
    they are 0.0 or 1.0 (which they very very rarely might be).
 *)

let sprod_neg (n,els) = ~-/n, els
 
let isneg_sprod (n,_ : sprod) = n</num_0

(* this only tells you if its representation starts with a minus sign *)
let printsneg_snum : snum -> bool = function
  | sprod::_ -> isneg_sprod sprod
  | []       -> false (* because it's zero *)

let sprod_1 = (num_1,[])

let snum_0 :snum = []

let snum_1 :snum = [sprod_1]

let sprod_half   = (half, [])

let snum_half = [sprod_half]

let s_el_h       = S_sqrt snum_half

let sprod_h      = (num_1,[s_el_h])

let sprod_half_h = (half, [s_el_h])

let snum_h :snum = [sprod_h]

let snum_oneplush = [sprod_1; sprod_h]

let snum_f :snum = [(num_1, [S_sqrt snum_half; S_sqrt snum_oneplush])]

let snum_oneminush = [sprod_1; sprod_neg sprod_h]

let snum_g :snum = [(num_1, [S_sqrt snum_half; S_sqrt snum_oneminush])]

let sprod_third   = (third, [])

let snum_third = [sprod_third]

let snum_t = [(num_1, [S_sqrt snum_third])]

let snum_symb symb :snum = [(num_1, [S_symb symb])]

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
  | S_sqrt x    -> Float.sqrt (to_float x)
  | S_symb symb -> float_of_symb symb

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
let rec string_of_root_num num =
  if num</num_0 then raise (Disaster (Printf.sprintf "string_of_root_num %s" (string_of_num num)))
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
  
and string_of_root sosnum snum =
  match numopt_of_snum snum with
  | Some num -> string_of_root_num num
  | _        -> Printf.sprintf "√(%s)" (sosnum snum)

and string_of_el_struct el = 
  match el with
  | S_sqrt snum -> string_of_root string_of_snum_struct snum
  | S_symb symb -> Printf.sprintf "{alpha=%B; imr=%B idsecret=%s}" 
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
      | S_sqrt n    -> string_of_root string_of_snum n
      | S_symb symb -> symbf symb
  
and string_of_el el = so_el string_of_symb el

and so_els symbf es = String.concat "" (List.map (so_el symbf) es)

and string_of_els es = 
  (match !fancynum with
   | RawNum -> string_of_els_struct
   | _      -> so_els string_of_symb 
  ) es

(* I want to get this right once, so I can deal with real and imaginary products.
   si is "" or "i"
 *)  
and so_prodi si symbf (n,els) = 
  match !fancynum with
  | RawNum        -> si ^ "*" ^ string_of_prod_struct (n,els)
  | FractionalNum ->
      let rec rc_els bra = function
        | S_sqrt n :: els -> let s = string_of_root string_of_snum n in
                             (if bra then "(" ^ s ^ ")" else s) ^ rc_els true els
        | S_symb s :: els -> symbf s ^ rc_els true els
        | []              -> ""
      in
      let rcstring () =
        if n=/num_1 && els<>[] then rc_els false els
                               else string_of_num n ^ rc_els true els 
      in
      if n</num_0         then "-" ^ so_prodi si symbf (~-/n,els)   else
      if n=/num_0         then "0" (* shouldn't happen *)           else
      if not !rootcombine then rcstring ()                          else
                               (let rec roots accum els =
                                  match els with
                                  | S_sqrt n :: els' -> (match numopt_of_snum n with 
                                                         | Some num -> roots (num*/accum) els'
                                                         | None     -> let accum, els'' = roots accum els' in
                                                                       accum, S_sqrt n :: els''
                                                        )
                                  | _                -> accum, els
                                in
                                let sq, els = roots (n*/n) els in
                                if els=[]           then string_of_root_num sq                                       else 
                                if sq=/num_1        then so_els symbf els                                            else
                                if sq.den=:z_1      then string_of_root_num sq ^ so_els symbf els                    else
                                if sq.num=:z_1      then so_els symbf els ^ "/" ^ string_of_root_num (reciprocal sq) else
                                                         "(" ^ string_of_root_num sq ^ ")" ^ so_els symbf els
                               )

and string_of_prod p = so_prodi "" string_of_symb p 

and fracparts (s:snum) : string list = List.map string_of_prod s

and string_of_snum (s:snum) = 
  match !fancynum with
  | RawNum        -> string_of_snum_struct s
  | FractionalNum -> sum_separate (fracparts s)

and string_of_snums snums = bracketed_string_of_list string_of_snum snums

(* The normal form -- now the snum type -- is a sum of products. 
 * Sign is now naturally included in the num element of a product.
 * I would like to sort snums so that the same el lists are adjacent but otherwise 
 * largest num first, as in the prodcompare function that used to be in simplify_sum.
 * Otherwise sqrts before symbs, and the natural ordering on symbs (because alpha
 * and imr fields are designed for it).
 *
 * But ... sqrts have snums in them! So I think I need a fancy function or two.
 *)

let (<??>) : int -> ('a -> int) -> ('a -> int)  =
             fun i f -> if i=0 then f else (fun _ -> i)

let revcompare a b = ~- (Stdlib.compare a b)

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

and prodcompare : sprod -> sprod -> int =
  fun (n1,els1) (n2,els2) -> (elscompare els1 els2 <??> ((~-) <.> Stdlib.compare n1)) n2 
  
and elscompare : s_el list -> s_el list -> int = 
  fun els1 els2 -> listcompare elcompare els1 els2

and elcompare : s_el -> s_el -> int = 
  fun x y ->
    match x, y with
    | S_sqrt nx, S_sqrt ny -> snumcompare nx ny
    | S_symb sx, S_symb sy -> Stdlib.compare sx sy
    | S_sqrt _ , S_symb _  -> ~-1
    | S_symb _ , S_sqrt _  -> 1
    

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
  
and simplify_prod (n,els as prod) :snum = (* We deal with sqrt^2, f^2, g^2, gh, fg *)
  let r = let rec sp els n ss = 
            if !verbose_simplify then 
              Printf.printf "sp %s %s %s\n" (string_of_els els) (string_of_num n) (string_of_els ss);
            let premult s n ss = 
              let popt, n, ss = sp els n ss in
              (match popt with 
               | Some pre_p -> Some (rprod pre_p s)
               | None       -> Some s
              ), n, ss
            in
            match ss with
            | S_sqrt a :: S_sqrt b :: ss 
              when a=b                   -> premult a n ss
            | S_sqrt [a;b] :: S_sqrt [a';b'] :: ss 
              when a=a'&&b=sprod_neg b' || 
                   b=b'&&a=sprod_neg a'  -> premult [num_1, [S_sqrt (rsum (rprod [b] [b']) (rprod [a] [a']))]] n ss (* √(a^2-b^2) *)
            | s                    :: ss -> sp (s::els) n ss
            | []                         -> None, n, List.sort elcompare els (* was List.rev els, but I think not needed *)
          in
          let popt, n, ss = sp [] n (List.sort elcompare els) in
          let s = [(n, List.sort elcompare ss)] in
          match popt with 
          | Some pre_p -> rprod pre_p s (* it does go round again! *)
          | None       -> s
  in
  if !verbose_simplify then
    Printf.printf "simplify_prod %s -> %s\n" (string_of_prod prod) (string_of_snum r);
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
              Printf.printf "multiple (%s) %s -> %s\n" (string_of_prod (n,els))  
                                                       (bracketed_string_of_list string_of_prod rest)
                                                       (string_of_pair string_of_num (bracketed_string_of_list string_of_prod) "," r);
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
                    Printf.printf "a2b2.find looking for %s (b.re*b.re) in %s\n" (string_of_prod p') (string_of_snum ps);
                  if List.exists ((=) p') ps 
                  then (
                    (* we have also found b.re*b.re *)
                    let ps' = Listutils.remove p' ps in
                    (* search for a.im*a.im and b.im*b.im *)
                    let pa' = remake (S_symb {symb1 with imr=true} :: S_symb {symb2 with imr=true} :: els) in
                    if !verbose_simplify then 
                      Printf.printf "a2b2.find looking for %s (a.im*a.im) in %s\n" (string_of_prod pa') (string_of_snum ps);
                    if List.exists ((=) pa') ps' then (
                      let pb' = remake (S_symb {symb1 with alpha=true; imr=true} :: S_symb {symb2 with alpha=true; imr=true} :: els) in
                      if !verbose_simplify then 
                        Printf.printf "a2b2.find looking for %s (b.im*b.im) in %s\n" (string_of_prod pb') (string_of_snum ps);
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
                                                (string_of_option (bracketed_string_of_pair string_of_prod string_of_snum) r);
            r
          in
          let rec twoh_etc fg p ps = (* looking for 2h√(1+h) or 2h√(1-h) *)
                                     (* fg is either 1+h or 1-h, and the answer is correspondingly √(1+h)+√(1-h) or √(1+h)-√(1-h) *)
                                     (* .. this could/must be generalised but I don't know how *)
            let n, els = p in
            let rec find num pres els =
              match els with
              | (S_sqrt n as el') :: els' 
                when num=n                -> Some (pres, el', els') 
              | el'               :: els' -> find num (el'::pres) els'
              | []                        -> None
            in
            if !verbose_simplify then Printf.printf "twoh_etc looking for 2h%s in %s\n" (string_of_el (S_sqrt fg)) (string_of_prod p);
            find snum_half [] els &~~
              (fun (pres, _, tail) -> 
                 if !verbose_simplify then Printf.printf "twoh_etc found h -- looking for %s in %s\n" (string_of_el (S_sqrt fg)) (string_of_els tail);
                 find fg pres tail &~~
                  (fun (pres,el_rootoneplush,tail) ->
                    let nb = if fg=snum_oneplush then num_1 else ~-/num_1 in
                    let pa = (n//num_2, Listutils.prepend pres (S_sqrt snum_oneplush::tail)) in
                    let pb = ((nb*/n)//num_2, Listutils.prepend pres (S_sqrt snum_oneminush::tail)) in
                    if !verbose_simplify then Printf.printf "twoh_etc success -- result %s\n" (string_of_snum [pa; pb]);
                    Some (pa, pb::ps)
                  ) 
              )
          in
          let rec sps again (r:sprod list) (ps:sprod list) =
            if !verbose_simplify then 
              Printf.printf "sps %B %s %s\n" again (string_of_snum r) (string_of_snum ps);
            match ps with
            | (n1,es1) :: (n2,es2) :: ps 
              when es1=es2                         -> let n', ps' = multiple (n1+/n2,es1) ps in
                                                      if n'=/num_0 then sps true r ps' else sps true ((n',es1)::r) ps'
             
            (* we try 2h√(1+h)=√(1+h)+√(1-h); 2h√(1-h)=√(1+h)-√(1-h); and a^2+b^2=1 *) 
            | p                  :: ps            -> (match twoh_etc snum_oneplush p ps 
                                                       |~~ (fun _ -> twoh_etc snum_oneminush p ps)
                                                       |~~ (fun _ -> a2b2 p ps) with
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
let reciprocal_sqrt (n:num) = [(reciprocal n, [S_sqrt [n,[]]])]

let rdiv_sqrt sn n = 
  rprod (reciprocal_sqrt n) sn

  
(******** snum arithmetic is where all the action is. So we memoise sum and prod, carefully *********)

module SnumH = struct type t = snum 
                      let equal = (=)
                      let hash = Hashtbl.hash
                      let to_string = string_of_snum
               end
module SnumHash = MyHash.Make (SnumH)

let memofunProb f str = 
  let table = SnumHash.create 100 in
  SnumHash.memofun table (fun s -> let r = f s in
                                   if !verbose || !verbose_simplify || !verbose_memo then 
                                      Printf.printf "memofun %s (%s) -> %s\n" str (string_of_snum s) (string_of_snum r); 
                                   r
                         )

let memofun2Prob f str = 
  let t1 = SnumHash.create 100 in
  SnumHash.memofun t1 
    (fun s1 -> let t2 = SnumHash.create 100 in
               SnumHash.memofun t2 
                 (fun s2 -> let r = f s1 s2 in
                            if !verbose || !verbose_simplify || !verbose_memo 
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
let memo_rsum = memofun2Prob rsum "rsum"

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
let memo_simplify_sum = memofunProb simplify_sum "simplify_sum"

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
                       | S_sqrt n -> (match numopt_of_snum n with
                                      | Some num -> Q.div n1 num, el::els1
                                      | _        -> bad ()
                                     )
                       | _        -> bad ()
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
                                                                                    (List.map string_of_prod ys)
                                                                 )
                                                  ^ ")"]
              in
              Listutils.prepend ss (fracparts xs @ ypart)
          | (n,ps as x)::xs, _  -> 
              let default () = parts ypres (string_of_prod x :: ss) (xs,ys) in
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
let c_f = csnum_of_snum snum_f
let c_g = csnum_of_snum snum_g

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
        let c_r_div_h = memofunC c_r_div_h "c_r_div_h"
     *)
 *)

