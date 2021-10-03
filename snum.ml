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
        
        f/h-f = g
        gh^3  = gfg = fg^2 -- not used
        gh = f(1-h)
        
   Also f^2+g^2 = 1 (which will fall out of the above)
 *)

(* for a long time this was a very ordinary data type. Now optimised for simplification (I hope) *)
type s_el = 
  | S_f              
  | S_g 
  | S_symb of s_symb                 (* k, false=a_k, true=b_k, conjugated, both random floats s.t. a_k**2+b_k**2 = 1; random r s.t. 0<=r<=1.0 *)

and s_symb = { id: int; alpha: bool; conj: bool; secret: float*float}

and sprod = bool * int * s_el list  (* true if neg, power of h, elements - a product*)

and snum = sprod list               (* a sum *) 

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
    
    We need both floats -- one for a, one for b -- because of the a2b2 function in simplify_prod.
 *)

let snum_0 :snum = []

let snum_1 :snum = [(false,0,[])]

let sprod_h n :sprod = (false,n,[])

let snum_h n :snum = [sprod_h n]

let snum_f :snum = [(false,0,[S_f])]

let snum_g :snum = [(false,0,[S_g])]

let snum_symb symb :snum = [(false,0,[S_symb symb])]

let isneg_sprod (s,_,_ : sprod) = s

let isneg_snum : snum -> bool = function
  | sprod::_ -> isneg_sprod sprod
  | []       -> false (* because it's zero *)
  
let string_of_el_struct = function
  | S_f         -> "f"            
  | S_g         -> "g"
  | S_symb symb -> let a,b = symb.secret in
                   Printf.sprintf "{id=%d; alpha=%B; conj=%B secret=(%f,%f)}" 
                            symb.id symb.alpha symb.conj a b

let string_of_els_struct = bracketed_string_of_list string_of_el_struct

let string_of_prod_struct = bracketed_string_of_triple string_of_bool string_of_int string_of_els_struct 

let string_of_snum_struct = bracketed_string_of_list string_of_prod_struct 

let string_of_snum_structs = bracketed_string_of_list string_of_snum_struct 

let string_of_el e = 
  match !fancynum with
  | RawNum -> string_of_el_struct e
  | _      ->
      match e with
      | S_f         -> "f"            
      | S_g         -> "g"
      | S_symb symb -> Printf.sprintf "%s%s%s%s" (if symb.alpha then "b" else "a") 
                                  (string_of_int symb.id) 
                                  (if symb.conj then " " else "")
                                  (if !showabvalues then let a, b = symb.secret in Printf.sprintf "[%f,%f]" a b else "")
  
let string_of_els es = 
  (match !fancynum with
   | RawNum -> String.concat "*" <.> List.map string_of_el 
   | _      -> string_of_els_struct
  ) es
  
let rec string_of_prod p = 
  if !fancynum<>RawNum then
    match p with
    | true, hn, els  -> "-" ^ string_of_prod (false, hn, els)
    | _   , 0 , []   -> "1"
    | _   , 1 , []   -> "h"
    | _   , hn, []   -> Printf.sprintf "h(%d)" hn
    | _   , 0 , els  -> string_of_els els
    | _   , hn, els  -> Printf.sprintf "%s*%s" (string_of_prod (false,hn,[])) (string_of_els els)
  else string_of_prod_struct p
  
let hpower_string_of_snum (s:snum) = 
  let prodstrings = List.map string_of_prod s in
  let ensign str = if str.[0]='-' then str else "+" ^ str in
  (match prodstrings with
   | []        -> "0"
   | [str]     -> str
   | str::strs -> str ^ (String.concat "" (List.map ensign strs))
  )

let fracparts (s:snum) : string list =
  let fpart ((neg, hpower, els) : sprod) = 
    let rem = hpower land 1 in (* rem 0 or 1: mod does it the horrid way *)
    let quot = (hpower-rem) / 2 in
    let frac = half **/ quot in
    (if neg then ~-/frac else frac), (false, rem, els)
  in
  let parts = List.map fpart s in
  let parts = List.sort (fun (_,na) (_,nb) -> Stdlib.compare na nb) parts in
  let rec fnparts revfps = function
    | []          -> List.rev revfps
    | (_,n) :: _ ->
        let sames, rest = takedropwhile (fun (_, n') -> n=n') parts in
        let f = List.fold_left (+/) num_0 (List.map fst sames) in
        (* f can be neg or pos; n is always pos *)
        fnparts ((f,n)::revfps) rest
  in
  let parts = fnparts [] parts in
  let spart (f,n) = 
    if [n]=snum_1 then string_of_num f else
      let num = Q.num f in
      let den = Q.den f in
      let nstr = hpower_string_of_snum [n] in
        (if num = Z.one then nstr else 
         if num = Z.minus_one then "-" ^ nstr else
         Z.to_string num ^ (if [n]=snum_1 then "" else nstr)
        ) ^
        (if den = Z.one then "" else "/" ^ Z.to_string den)
  in
  List.map spart parts

let rec sum_separate = function
  | s1::s2::ss -> if Stringutils.starts_with s2 "-" then s1 ^ sum_separate (s2::ss) 
                  else s1 ^ "+" ^ sum_separate (s2::ss) 
  | [s]        -> s
  | []         -> "0" (* oh yes it can happen ... raise (Can'tHappen "sum_separate []") *)

let string_of_snum (s:snum) = 
  match !fancynum with
  | RawNum        -> string_of_snum_struct s
  | HpowerNum     -> hpower_string_of_snum s
  | FractionalNum -> sum_separate (fracparts s)

let string_of_snums = bracketed_string_of_list string_of_snum

(* *********************** symbolic arithmetic ************************************ *)

(* The normal form -- now the snum type -- is a sum of possibly-negated products. 
 * Products are sorted according to the type definition: i.e.
 * S_f, S_g, S_symb. 
 
 * We sort identifiers according to their suffix: a0,b0,a1,b1, ...
 
 * Stdlib.compare works if we change the definition of S_symb, so I did
 
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
let rconj (s:snum) = 
  let rec rc_el = function
    | S_f              
    | S_g           -> None
    | S_symb symb   -> Some (S_symb {symb with conj=not symb.conj})
  and rc_prod (sign,hn,els) =
    optmap_any rc_el els &~~ (fun els' -> Some (sign,hn,els'))
  in
  if !complexunknowns then (optmap_any rc_prod ||~ id) s else s

let sprod_neg (sign,hn,els) = not sign, hn, els

let rec rneg s =
  let r = List.map sprod_neg s in
  if !verbose_simplify then
    Printf.printf "rneg (%s) -> %s\n" (string_of_snum s) (string_of_snum r);
  r
    
and rprod s1 s2 :snum =
  let rp (sign1,hn1,els1) (sign2,hn2,els2) = simplify_prod (sign1<>sign2, hn1+hn2, els1@els2) in
  let r = simplify_sum 
            (List.fold_left 
               (fun sum prod1 -> List.fold_left (fun sum prod2 -> (rp prod1 prod2) @ sum) sum s2)
               []
               s1
            )
  in
  if !verbose_simplify then
    Printf.printf "rprod (%s) (%s) -> %s\n" (string_of_snum s1) (string_of_snum s2) (string_of_snum r);
  r
  
and simplify_prod (sign,hn,els as prod) :snum = (* We deal with f^2, g^2, gh, fg *)
  let r = let rec sp els hn ss = 
            let premult s hn ss = 
              let popt, hn, ss = sp els hn ss in
              (match popt with 
               | Some pre_p -> Some (rprod pre_p s)
               | None       -> Some s
              ), hn, ss
            in
            match ss with
            | S_f   :: S_f   :: ss -> premult [sprod_h 2; sprod_h 3] hn ss
            | S_f   :: S_g   :: ss -> premult [sprod_h 3] hn ss
            | S_g   :: S_g   :: ss -> premult [sprod_h 2; sprod_neg (sprod_h 3)] hn ss
(*          | S_g   ::          ss    (* prefer f to g: gh^3 is gfg = fg^2 *)
              when hn>=3           -> sp (S_f :: els) (hn-3) (S_g :: S_g :: ss)) 
 *)
            | S_g   ::          ss    (* prefer f to g: gh^3 is gfg = fg^2 = f(h^2-h^3) so gh = f(1-h) *)
              when hn>=1           -> premult [sprod_h 0; sprod_neg (sprod_h 1)] (hn-1) (S_f :: ss)
            | s              :: ss -> sp (s::els) hn ss
            | []                   -> None, hn, sort Stdlib.compare els
          in
          let popt, hn, ss = sp [] hn (sort Stdlib.compare els) in
          let s = [(sign, hn, ss)] in
          match popt with 
          | Some pre_p -> rprod pre_p s
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
  let r = let prodcompare (sg1,hn1,els1) (sg2,hn2,els2) = (* ignore negation, but put -p after p *)
            Stdlib.compare (hn1,els1,sg1) (hn2,els2,sg2) 
          in
          let rec multiple p rest = (* looking for X+X+... -- we no longer care about the h's *)
            let r = (match takedropwhile ((=)p) rest with
                     | [] , _   -> None (* not going to happen, but never mind *)
                     | ps, rest -> Some (rmult_zint [p] (zlength ps+:z_1), rest)
                    )
            in
            if !verbose_simplify then
              Printf.printf "multiple (%s) %s -> %s\n" (string_of_prod p)  
                                                       (bracketed_string_of_list string_of_prod rest)
                                                       (string_of_option (string_of_pair string_of_snum (bracketed_string_of_list string_of_prod) ",") r);
            r
          in
          let rec a2b2 p ps = (* looking for X*aa!Y+X*bb!Y to replace with XY. Sorting doesn't always make aa! and bb! next to each other in ps *)
            let sign,hn,els = p in
            let rec find pres els =
              match els with 
              | S_symb ({id=q1; alpha=false; conj=false} as symb1) :: 
                S_symb ({id=q2; alpha=false; conj=c    } as symb2) :: els 
                          when q1=q2 && c = !complexunknowns 
                          -> 
                  let remake post = sign, hn, prepend pres post in
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
          let rec sp again (r:sprod list) (ps:sprod list) =
            if !verbose_simplify then 
              Printf.printf "sp %B %s %s\n" again (string_of_snum r) (string_of_snum ps);
            match ps with
            (* negated but otherwise identical *)
            | (sg1,hn1,es1) :: (sg2,hn2,es2) :: ps when hn1=hn2 && es1=es2 && sg1<>sg2 -> sp true r ps
            (* the next two are because h^j-h^(j+2) = h^j(1-h^2) = h^(j+2) 
               -- and for confluence, dammit, I have to do the h(j)+h(j+2) = h(j-2)-h(j+2) thing. Rats. 
             *)
            | (sg,j,es) ::  ps  
                    when List.exists ((=) (not sg,j+2,es)) ps
                                                  -> sp true ((sg,j+2,es)::r) (Listutils.remove (not sg,j+2,es) ps)
            | (sg,j,es) ::  ps  
                    when List.exists ((=) (sg,j+2,es)) ps
                                                  -> sp true ((not sg,j+2,es)::(sg,j-2,es)::r) (Listutils.remove (sg,j+2,es) ps)
            (* f(1-h) = gh *)
            | (sg,j,(S_f :: es)) :: ps
                   when List.exists ((=) (not sg,j+1,S_f :: es)) ps
                                                  -> sp true ((sg,j+1,S_g :: es) :: r) 
                                                             (Listutils.remove (not sg,j+1,S_f :: es) ps)
            (* many copies of the same thing *)
            | p1      :: p2      :: ps when p1=p2 -> (match multiple p1 (p2::ps) with
                                                      | Some (s,ps) -> sp true (s@r) ps
                                                      | None        -> sp again (p1::r) (p2::ps)
                                                     )
            (* last desperate throw: a^2+b^2 *) (* should it happen here? *)
            | p                  :: ps            -> (match a2b2 p ps with
                                                      | Some (p', ps') -> sp true (p'::r) ps'
                                                      | None           -> sp again (p::r) ps
                                                     )
            | []                                  -> if again then doit r else sort prodcompare r
          and doit ps = sp false [] (sort prodcompare ps)
          in
          doit ps
  in
  if !verbose_simplify then
    Printf.printf "simplify_sum (%s) -> %s\n" (string_of_snum ps) (string_of_snum r);
  r

and rmult_zint sn zi =
  if sn=snum_0 || Z.(zi=zero) then snum_0 else
  if Z.(zi<zero) then rneg (rmult_zint sn Z.(~-zi))
                 else match setbits zi with
                      | []  -> snum_0
                      | [0] -> sn
                      | bs  -> rprod sn (List.map (fun i -> sprod_h (-2*i)) bs)
  
and rdiv_h s = rprod (snum_h (-1)) s (* multiply by h(-1) = divide by h(1). Used to happen in normalise; may happen again in try_split *)
  
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
    (* we do 0, 1 and -1 ourselves *)
    | []          , _
    | _           , []           -> []   
    | [false,0,[]], _            -> s2
    | _           , [false,0,[]] -> s1
    | [true ,0,[]], _            -> rneg s2
    | _           , [true ,0,[]] -> rneg s1
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
    | []      , _       -> s2
    | _       , []      -> s1
   (* (* we memoise sum *)
    | S_sum  _ , _
    | _       , S_sum  _ -> memo_rsum s1 s2
    (* everything else is raw *)
    | _                 -> raw_rsum s1 s2 *)
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
  let im y = (* y non-zero, positive *)
    match y with
    | [_,0,[]]    -> "i"
    | [_,_,_]     -> "i*" ^ string_of_snum y
    | _           -> "i*(" ^ string_of_snum y ^ ")"
  in
  match x,y with
  | [] , []            -> "0"
  | _  , []            -> string_of_snum x
  | [] , (true,_,_)::_ -> "-" ^ im (rneg y)
  | [] , _             -> im y
  | _  , (true,_,_)::_ -> "(" ^ string_of_snum x ^ "-" ^ im (rneg y) ^ ")"
  | _  , _             -> "(" ^ string_of_snum x ^ "+" ^ im y ^ ")"

let csnum_of_snum s = C (s, snum_0)

let c_0 = csnum_of_snum snum_0
let c_1 = csnum_of_snum (snum_1)
let c_h = csnum_of_snum (snum_h 1)
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
  match x1,y1, x2,y2 with
  | []           , [] , _            , _    
  | _            , _  , []           , []        -> c_0
  | [false,0,[]] , [] , _            , _         -> c2  
  | _            , _  , [false,0,[]] , []        -> c1
  | [true ,0,[]] , [] , _            , _         -> cneg c2  
  | _            , _  , [true ,0,[]] , []        -> cneg c1
  | _            , [] , _            , []        -> intern (C (rprod x1 x2, []))             (* real    * real    *)
  | _            , [] , _            , _         -> intern (C (rprod x1 x2, rprod x1 y2))    (* real    * complex *)
  | _            , _  , _            , []        -> intern (C (rprod x1 x2, rprod y1 x2))    (* complex * real    *)
  | _                                            -> intern (C (rsum (rprod x1 x2) (rneg (rprod y1 y2)), rsum (rprod x1 y2) (rprod y1 x2)))

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

