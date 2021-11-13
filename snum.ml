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

and s_symb = { id: int; alpha: bool; conj: bool; secret: float*float}
             (* k,      false=a_k, true=b_k, 
                                     conjugated, both random floats s.t. a_k**2+b_k**2 = 1; 
                                                      each s.t. 0<=float<=1.0 *)
             
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

let snum_0 :snum = []

let snum_1 :snum = [(num_1,[])]

let sprod_half   = (half, [])

let s_el_h       = S_sqrt half

let sprod_h      = (num_1,[s_el_h])

let sprod_half_h = (half, [s_el_h])

let snum_h :snum = [sprod_h]

let snum_t :snum = [(num_1,[S_sqrt third])]

let sprod_f      = (num_1,[S_f])
let sprod_hf     = (num_1,[s_el_h; S_f])

let snum_f :snum = [sprod_f]

let snum_g :snum = [(num_1,[S_g])]

let snum_symb symb :snum = [(num_1,[S_symb symb])]

(* not used

   let isneg_sprod (n,_ : sprod) = n</num_zero

   let isneg_snum : snum -> bool = function
     | sprod::_ -> isneg_sprod sprod
     | []       -> false (* because it's zero *)
 *)  

let string_of_el_struct = function
  | S_sqrt n    -> Printf.sprintf "r(%s)" (string_of_num n)
  | S_f         -> "f"            
  | S_g         -> "g"
  | S_symb symb -> let a,b = symb.secret in
                   Printf.sprintf "{id=%d; alpha=%B; conj=%B secret=(%f,%f)}" 
                            symb.id symb.alpha symb.conj a b

let string_of_els_struct = bracketed_string_of_list string_of_el_struct

let string_of_prod_struct = bracketed_string_of_pair string_of_num string_of_els_struct 

let string_of_snum_struct = bracketed_string_of_list string_of_prod_struct 

let string_of_snum_structs = bracketed_string_of_list string_of_snum_struct 

let string_of_el e = 
  match !fancynum with
  | RawNum -> string_of_el_struct e
  | _      ->
      match e with
      | S_sqrt n    -> if n=/half  then "h"     else
                       if n=/third then "t"     else
                                        Printf.sprintf "r(%s)" (string_of_num n)
      | S_f         -> "f"            
      | S_g         -> "g"
      | S_symb symb -> Printf.sprintf "%s%s%s%s" (if symb.alpha then "b" else "a") 
                                  (string_of_int symb.id) 
                                  (if symb.conj then " " else "")
                                  (if !showabvalues then let a, b = symb.secret in Printf.sprintf "[%f,%f]" a b else "")
  
let string_of_els es = 
  (match !fancynum with
   | RawNum -> string_of_els_struct
   | _      -> String.concat "" <.> List.map string_of_el 
  ) es

(* I want to get this right once, so I can deal with real and imaginary products.
   si is "" or "i"
 *)  
  
let rec string_of_prodi si (n,els) = 
  if !fancynum<>RawNum then 
    (if n</num_0   then "-" ^ string_of_prodi si (~-/n,els) else
     if n=/num_0   then "0" (* shouldn't happen *)          else
                        (let numerator = 
                           match n.num=:z_1, si, els with
                           | true , "", [] -> "1"
                           | true , _ , _  -> si ^ string_of_els els
                           | false, _ , _  -> string_of_zint n.num ^ si ^ string_of_els els
                         in
                         numerator ^ if n.den=z_1 then "" else ("/" ^ string_of_zint n.den)
                        )
    )
  else 
    si ^ string_of_prod_struct (n,els)

let string_of_prod p = string_of_prodi "" p 

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

let fp_h2 = 0.5
let fp_h = sqrt fp_h2
let fp_f2 = (1.0 +. fp_h) /. 2.0
let fp_f = sqrt fp_f2
let fp_g2 = (1.0 -. fp_h) /. 2.0
let fp_g = sqrt fp_g2

let rec to_float = 
  let compute_el = function
    | S_sqrt x    -> sqrt (Q.to_float x)
    | S_f         -> fp_f
    | S_g         -> fp_g
    | S_symb symb -> let a,b = symb.secret in if symb.alpha then b else a
  in
  let compute_prod (n,els) =
    Q.to_float n *. (List.fold_left ( *. ) 1.0 (List.map compute_el els))
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

(* an snum is usually a real. But not always ... *)
let rconj (s:snum) = 
  let rec rc_el = function
    | S_sqrt _
    | S_f              
    | S_g           -> None
    | S_symb symb   -> Some (S_symb {symb with conj=not symb.conj})
  and rc_prod (n,els) =
    optmap_any rc_el els &~~ (fun els' -> Some (n,els'))
  in
  if !complexunknowns then (optmap_any rc_prod ||~ id) s else s

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
            | S_sqrt a   :: S_g    :: ss    (* prefer f to g: gh^3 is gfg = fg^2 = f(h^2-h^3) so hg = f(1-h) *)
              when a=/half               -> premult [sprod_f; sprod_neg sprod_hf] n ss
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
            let n,els = p in
            let rec find pres els =
              match els with 
              | S_symb ({id=q1; alpha=false; conj=false} as symb1) :: 
                S_symb ({id=q2; alpha=false; conj=c    } as symb2) :: els 
                          when q1=q2 && c = !complexunknowns 
                          -> 
                  let remake post = n, prepend pres post in
                  let p' = remake (S_symb {symb1 with alpha=true} :: S_symb {symb2 with alpha=true} :: els) in
                  if !verbose_simplify then 
                    Printf.printf "a2b2.find looking for %s in %s\n" (string_of_prod p') (string_of_snum ps);
                  if List.exists ((=) p') ps then Some (remake els, Listutils.remove p' ps)
                                             else find (S_symb symb2::S_symb symb1::pres) els
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
            (* f(1-h) = gh -- commented out for now 
            | (sg,j,(S_f :: es)) :: ps
                   when List.exists ((=) (not sg,j+1,S_f :: es)) ps
                                                  -> sps true ((sg,j+1,S_g :: es) :: r) 
                                                             (Listutils.remove (not sg,j+1,S_f :: es) ps)
             *)
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

(* can't do this any more -- at least not this way
   and rdiv_h s = rprod (snum_h (-1)) s (* multiply by h(-1) = divide by h(1). Used to happen in normalise; may happen again in try_split *)
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

  
(* *********************** complex arith in terms of reals ************************************ *)

type csnum = C of snum*snum (* complex snum A + iB *)

let string_of_csnum (C (x,y)) =
  let rec im y = (* y non-zero *) 
    match y with
    | [p]                -> string_of_prodi "i" p
    | _                  -> "i*(" ^ string_of_snum y ^ ")"
  in
  match x,y with
  | [] , []            -> "0"
  | _  , []            -> string_of_snum x
  | [] , _             -> im y
  | _  , _             -> sum_separate [string_of_snum x; im y]

let csnum_of_snum s = C (s, snum_0)

let c_0 = csnum_of_snum snum_0
let c_1 = csnum_of_snum (snum_1)
let c_h = csnum_of_snum (snum_h)
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

let csum  (C (x1,y1) as c1) (C (x2,y2) as c2) = 
  match x1,y1, x2,y2 with
  | [] , [] , _  , _    -> c2 
  | _  , _  , [] , []   -> c1
  | _                   -> intern (C (rsum x1 x2, rsum y1 y2))

let simplify_csum = function
  | [] -> c_0
  | cs -> let reals, ims = List.split (List.map (fun (C (x,y)) -> x,y) cs) in
          C (simplify_sum (sflatten reals), simplify_sum (sflatten ims))  

let cdiff c1 c2 = csum c1 (cneg c2)

let cconj (C(x,y)) = intern (C (rconj x, rneg (rconj y)))

let absq  (C(x,y) as c) = (* this is going to cost me ... *)
  let x',y' = rconj x, rconj y in
  if x=x' && y=y' || y=snum_0 then rsum (rprod x x') (rprod y y')
  else (let c' = cconj c in 
        if !verbose || !verbose_simplify then
          Printf.printf "**Here we go: |%s|^2 is (%s)*(%s)\n"
                              (string_of_csnum c)
                              (string_of_csnum c)
                              (string_of_csnum c');
        let C(rx,ry) as r = cprod c c' in
        if ry=snum_0 then (if !verbose || !verbose_simplify then Printf.printf "phew! that worked -- %s\n" (string_of_snum rx); 
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
    let c_r_div_h (C(x,y))            = intern (C (rdiv_h x, rdiv_h y))
 *)

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

