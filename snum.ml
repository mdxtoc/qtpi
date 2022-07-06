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
        
   Also f^2+g^2 = 1 (which will fall out of the above)
 *)

(* for a long time this was done in terms of h = sqrt (1/2). But that's embarrassing now.
   So: something more general, numbers, square roots, powers, sums and prods. Hoping to 
   make it work.
 *)
type s_el = 
  | S_sqrt of num
  | S_f                 (* keep f and g for now ... *)   
  | S_g 
  | S_symb of s_symb                 

and s_symb = {alpha: bool; imr: bool; idsecret: symrec} 
           (* false=a / true=b,
                           false=real / true=imaginary, 
                                      shared inf.
              -- note choice of false/true alternatives because false sorts before true,
                 so a before b, real before imaginary
            *)

and symrec = {id: int; secret: (float*float)*(float*float)} 
             (* k,     
                       secret amplitudes for a (re,im) and b (re,im)
                       -- note a before b, real before imaginary
                       -- never used in simplifying
                       -- total of the four must be 1.0
              *)
             
and sprod = num * s_el list         (* a product*)

and snum = sprod list               (* a sum *) 

(* S_symb is an unknown (with furtively a secret value -- see below). 
   0, 1, f and g are reals, but S_symb is a complex number. So it has a conjugate. 
   Hence the conj field.
   
   The order of the fields matters for sorting: 
    -- a1 comes before a2 (and b2, and etc.) so the id field is first; 
    -- ai comes before bi so the alpha field is second (and false means a);
    -- ai comes before ai! so the conj field is third;
    -- a secret amplitude value.
    
    The secret values are used when measuring, to compute the value of a formula
    involving the symbol. They are _never_ used when calculating/simplifying, even if
    they are 0.0 or 1.0 (which they very very rarely might be).
    
    We need both floats -- one for a, one for b -- because of the a2b2 function in simplify_prod.
 *)
let sprod_1 = (num_1,[])

let snum_0 :snum = []

let snum_1 :snum = [sprod_1]

let sprod_half   = (half, [])

let s_el_h       = S_sqrt half

let sprod_h      = (num_1,[s_el_h])

let sprod_half_h = (half, [s_el_h])

let snum_h :snum = [sprod_h]

let snum_t :snum = [(num_1,[S_sqrt third])]

let sprod_f      = (num_1,[S_f])
let sprod_fh     = (num_1,[S_f; s_el_h])

let snum_f :snum = [sprod_f]

let snum_g :snum = [(num_1,[S_g])]

let snum_symb symb :snum = [(num_1,[S_symb symb])]

let isneg_sprod (n,_ : sprod) = n</num_0

let isneg_snum : snum -> bool = function
  | sprod::_ -> isneg_sprod sprod
  | []       -> false (* because it's zero *)

let fp_h2 = 0.5
let fp_h = sqrt fp_h2
let fp_f2 = (1.0 +. fp_h) /. 2.0
let fp_f = sqrt fp_f2
let fp_g2 = (1.0 -. fp_h) /. 2.0
let fp_g = sqrt fp_g2

let float_of_symb symb = let a,b = symb.idsecret.secret in 
                         let re,im = if symb.alpha then b else a in (* false is a *)
                         if symb.imr then im else re                (* false is re *)
  
let float_of_el = function
  | S_sqrt x    -> sqrt (Q.to_float x)
  | S_f         -> fp_f
  | S_g         -> fp_g
  | S_symb symb -> float_of_symb symb

(* roots with square root and overline *)
let string_of_root num =
  let root n =
    let s = string_of_num n in
    let count = String.length s in
    let f i = if i mod 2 = 0 then String.make 1 s.[i/2] 
                             else String.init 2 (fun i -> Char.chr (if i=0 then 0xCC else 0x85)) (* Unicode overline *)
    in
    Printf.sprintf "√%s" (String.concat "" (Listutils.tabulate (2*count) f))
  in
  let numr, denr = numden_num num in
  if numr =/ num_1 then
    if denr =/ num_1 then "1"
    else Printf.sprintf "1/%s" (root denr)
  else
  root num
  
let string_of_symrec symrec =
  Printf.sprintf "{id=%d; secret=((%f,%f),(%f,%f))}"
                   symrec.id
                   (fst(fst symrec.secret)) (snd(fst symrec.secret))
                   (fst(snd symrec.secret)) (snd(snd symrec.secret))
                   
let string_of_el_struct = function
  | S_sqrt n    -> string_of_root n
  | S_f         -> "f"            
  | S_g         -> "g"
  | S_symb symb -> Printf.sprintf "{alpha=%B; imr=%B idsecret=%s}" 
                             symb.alpha symb.imr (string_of_symrec symb.idsecret)

let string_of_els_struct = bracketed_string_of_list string_of_el_struct

let string_of_prod_struct = bracketed_string_of_pair string_of_num string_of_els_struct 

let string_of_snum_struct = bracketed_string_of_list string_of_prod_struct 

let string_of_snum_structs = bracketed_string_of_list string_of_snum_struct 

let dagger_string = "†"
let re_string = "𝕣"
let im_string = "𝕚"

let string_of_symb symb =
  Printf.sprintf "%s%d%s%s" 
                 (if symb.alpha then "b" else "a") 
                 symb.idsecret.id 
                 (if symb.imr then im_string else re_string)
                 (if !showabvalues then Printf.sprintf "[%f]" (float_of_symb symb) else "")

let so_el symbf e = 
  match !fancynum with
  | RawNum -> string_of_el_struct e
  | _      ->
      match e with
      | S_sqrt n    -> if n=/half  && !symbolic_ht then "h"     else
                       if n=/third && !symbolic_ht then "t"     else
                       string_of_root n
      | S_f         -> "f"            
      | S_g         -> "g"
      | S_symb symb -> symbf symb
  
let string_of_el = so_el string_of_symb

let so_els symbf es = String.concat "" (List.map (so_el symbf) es)

let string_of_els es = 
  (match !fancynum with
   | RawNum -> string_of_els_struct
   | _      -> so_els string_of_symb 
  ) es

(* I want to get this right once, so I can deal with real and imaginary products.
   si is "" or "i"
 *)  
  
let rec so_prodi si symbf (n,els) = 
  match !fancynum with
  | RawNum        -> si ^ "*" ^ string_of_prod_struct (n,els)
  | FractionalNum ->
      if n</num_0   then "-" ^ so_prodi si symbf (~-/n,els) else
      if n=/num_0   then "0" (* shouldn't happen *)          else
                         (let numerator = 
                            match n.num=:z_1, si, els with
                            | true , "", [] -> "1"
                            | true , _ , _  -> si ^ so_els symbf els
                            | false, _ , _  -> string_of_zint n.num ^ si ^ so_els symbf els
                          in
                          numerator ^ if n.den=z_1 then "" else ("/" ^ string_of_zint n.den)
                         )

let string_of_prod p = so_prodi "" string_of_symb p 

let fracparts (s:snum) : string list = List.map string_of_prod s

let rec sum_separate = function
  | s1::s2::ss -> if Stringutils.starts_with s2 "-" then s1 ^ sum_separate (s2::ss) 
                  else s1 ^ "+" ^ sum_separate (s2::ss) 
  | [s]        -> s
  | []         -> "0" (* oh yes it can happen ... raise (Can'tHappen "sum_separate []") *)

let string_of_snum (s:snum) = 
  match !fancynum with
  | RawNum        -> string_of_snum_struct s
  | FractionalNum -> sum_separate (fracparts s)

let string_of_snums = bracketed_string_of_list string_of_snum

(* The normal form -- now the snum type -- is a sum of products. 
 * Sign is now naturally included in the num element of a product.
 * Products are sorted according to the type definition: i.e.
 * S_sqrt _, S_f, S_g, S_symb. (but somehow sqrt is coming last. Hmm.)
 
 * We sort identifiers according to their suffix: a0,b0,a1,b1, ...
 
 * Stdlib.compare works if we change the definition of S_symb, so I did
 
 *)

let elcompare = Stdlib.compare

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

let rec to_float = 
  let compute_prod (n,els) =
    Q.to_float n *. (List.fold_left ( *. ) 1.0 (List.map float_of_el els))
  in
  List.fold_left ( +. ) 0.0 <.> List.map compute_prod

(* we deal with long lists. Avoid sorting if poss *)
let sort compare ss =
  let rec check ss' =
    match ss' with
    | s'::(s''::_ as ss') -> if s'<s'' then check ss' else List.sort compare ss
    | _                   -> ss
  in
  check ss

let rmult_num sn n =
  if n=/num_0 then snum_0  else 
  if n=/num_1 then sn      else
  List.map (fun (m,els) -> n*/m,els) sn
  
let rmult_zint sn zi = rmult_num sn (num_of_zint zi)

let sprod_neg (n,els) = ~-/n, els

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
              when a=/b                  -> sp els (n*/a) ss
            | S_f      :: S_f      :: ss -> premult [sprod_half; sprod_half_h] n ss
            | S_f      :: S_g      :: ss -> premult [sprod_half_h] n ss
            | S_g      :: S_g      :: ss -> premult [sprod_half; sprod_neg (sprod_half_h)] n ss
(*          | S_g      ::             ss    (* prefer f to g: gh^3 is gfg = fg^2 *)
              when hn>=3                 -> sp (S_f :: els) (hn-3) (S_g :: S_g :: ss)) 
 *)
            | S_g      :: S_sqrt a :: ss    (* prefer f to g: gh^3 is gfg = fg^2 = f(h^2-h^3) so gh = f(1-h) -- may lead to 2fh-f *)
              when a=/half               -> premult [sprod_f; sprod_neg sprod_fh] n ss
            | s                    :: ss -> sp (s::els) n ss
            | []                         -> None, n, sort elcompare (List.rev els)
          in
          let popt, n, ss = sp [] n (sort elcompare els) in
          let s = [(n, sort elcompare ss)] in
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
  let r = let prodcompare (n1,els1) (n2,els2) = (* els before n, pos before neg *)
                  Stdlib.compare (els1,~-/n1) (els2,~-/n2) (* hmmm. *)
          in
          let multiple (n,els:sprod) rest = (* looking for nX+mX+... -- we sum the num parts *)
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
                          Printf.printf "a2b2.find success! (complex unknown)\n";
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
          let rec sps again (r:sprod list) (ps:sprod list) =
            if !verbose_simplify then 
              Printf.printf "sps %B %s %s\n" again (string_of_snum r) (string_of_snum ps);
            match ps with
            | (n1,es1) :: (n2,es2) :: ps 
              when es1=es2                         -> let n', ps' = multiple (n1+/n2,es1) ps in
                                                      if n'=/num_0 then sps true r ps' else sps true ((n',es1)::r) ps'
            (* 2fh-f = g  -- removes symbols *)
            | (n1,(S_f :: S_sqrt a :: es)) :: ps
                   when a=/half && List.exists ((=) (n1//(~-/num_2),S_f :: es)) ps
                                                  -> sps true ((n1//num_2,S_g :: es) :: r) 
                                                              (Listutils.remove (n1//(~-/num_2),S_f :: es) ps)
             
            (* last desperate throw: a^2+b^2 *) (* should it happen here? *)
            | p                  :: ps            -> (match a2b2 p ps with
                                                      | Some (p', ps') -> sps true (p'::r) ps'
                                                      | None           -> sps again (p::r) ps
                                                     )
            | []                                  -> if again then doit r else sort prodcompare r
          and doit ps = sps false [] (sort prodcompare ps)
          in
          doit ps
  in
  if !verbose_simplify then
    Printf.printf "simplify_sum (%s) -> %s\n" (string_of_snum ps) (string_of_snum r);
  r

(* given the wrong numbers, this will generate lots of strange S_sqrt entries ... 
   so be careful
 *)
let reciprocal_sqrt n = [(Number.reciprocal n, [S_sqrt n])]

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
                       | S_sqrt n -> Q.div n1 n, el::els1
                       | _        -> bad ()
                   in
                   let sn_div (n1,els1) = List.fold_left el_div (Q.div n1 n2, els1) els2 in
                   simplify_sum (List.map sn_div r1)
    | _         -> bad () (* can't divide by a sum *)
    
(* *********************** complex arith in terms of reals ************************************ *)

type csnum = C of snum*snum (* complex x + iy *)

let isneg_csnum = function
  | C([], y) -> isneg_snum y
  | C(x , _) -> isneg_snum x
  
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
              let rec treatable signopt ps = 
                match ps with
                | []    -> signopt
                | p::ps -> (match signopt, p with
                            | Some sign, S_symb s -> if sign=s.imr then treatable signopt ps else None
                            | None     , S_symb s -> treatable (Some s.imr) ps
                            | _                   -> treatable signopt ps
                           )
              in
              match !showunknownparts, treatable None ps with
              | true, _        
              | _   , None     -> default ()
              | _   , Some imr -> 
                  let rec sameps ps ps' =
                    match ps, ps' with
                    | p::ps, p'::ps' -> (match p, p' with
                                         | S_symb s, S_symb s' -> s={s' with imr=not s'.imr}
                                         | _                   -> p=p'
                                        ) && sameps ps ps'
                    | []   , []      -> true
                    | _              -> false
                  in
                  let rec findsame ypres ys =
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
let c_reciprocal_h = csnum_of_snum (reciprocal_sqrt Number.half)
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

