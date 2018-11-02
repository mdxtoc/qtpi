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

open Sourcepos
open Functionutils
open Listutils
open Interpret

(* ******************** built-in functions ********************* *)

(* This stuff is intended to be replaced by dynamically-loaded stuff,
   as soon as I can get round to understanding the mechanism.
 *)

let vfun2 f = vfun (fun a -> vfun (fun b -> f a b))
let vfun3 f = vfun (fun a -> vfun (fun b -> vfun (fun c -> f a b c)))

let funv2 f = funv <.> funv f

(* ******************** lists ********************* *)
let v_hd vs =
  let vs = listv vs in
  try List.hd vs with _ -> raise (LibraryError "hd []")

let v_tl vs =
  let vs = listv vs in
  try vlist (List.tl vs) with _ -> raise (LibraryError "tl []")
  
let v_append xs ys =
  let xs = listv xs in
  let ys = listv ys in
  vlist (List.append xs ys)
  
let v_fxs cf vf v2cf f xs =
  let f = funv f in
  let xs = listv xs in
  vf (cf (v2cf <.> f) xs)
;;

let v_iter = v_fxs List.iter vunit ignore

let v_map = v_fxs List.map vlist id

let v_filter = v_fxs List.filter vlist boolv

let v_exists = v_fxs List.exists vbool boolv

let v_forall = v_fxs List.for_all vbool boolv

let v_foldl f a xs = 
  let f = funv2 f in
  let xs = listv xs in
  List.fold_left f a xs
  
let v_foldr f a xs = 
  let f = funv2 f in
  let xs = listv xs in
  List.fold_right f xs a

let v_take n xs =
  let n = intv n in
  let xs = listv xs in
  vlist (Listutils.take n xs)
  
let v_takewhile p xs =
  let p = boolv <.> funv p in
  let xs = listv xs in
  vlist (Listutils.takewhile p xs)
  
let v_drop n xs =
  let n = intv n in
  let xs = listv xs in
  vlist (Listutils.drop n xs)

let rec v_dropwhile p xs =
  let p = boolv <.> funv p in
  let xs = listv xs in
  vlist (Listutils.dropwhile p xs)

let v_randbits n =
  let n = intv n in
  let rec randbits n =
    if n=0 then [] 
    else (let b = Random.bool () in
          vint (if b then 1 else 0)::randbits (n-1)
         ) 
  in
  vlist (randbits n)

let v_zip xs ys = try vlist (List.map vpair (List.combine (listv xs) (listv ys))) 
                  with Invalid_argument _ -> raise (LibraryError (Printf.sprintf "zip (%d %d) %s %s"
                                                                                 (List.length (listv xs))
                                                                                 (List.length (listv ys))
                                                                                 (bracketed_string_of_list string_of_value (listv xs))
                                                                                 (bracketed_string_of_list string_of_value (listv ys))
                                                          )
                                                   )

let v_unzip xys = let xs, ys = List.split (List.map pairv (listv xys)) in
                  vpair (vlist xs, vlist ys)

let v_concat xss = vlist (List.concat (List.map listv (listv xss)))

let _ = Interpret.know ("length"   , "'a list -> int                        ", vfun (vint <.> List.length <.> listv))

let _ = Interpret.know ("hd"       , "'a list -> 'a                         ", vfun v_hd)
let _ = Interpret.know ("tl"       , "'a list -> 'a list                    ", vfun v_tl)

let _ = Interpret.know ("rev"      , "'a list -> 'a list                    ", vfun (vlist <.> List.rev <.> listv))
let _ = Interpret.know ("append"   , "'a list -> 'a list -> 'a list         ", vfun2 v_append)

let _ = Interpret.know ("iter"     , "('a -> unit) -> 'a list -> unit       ", vfun2 v_iter)
let _ = Interpret.know ("map"      , "('a -> 'b) -> 'a list -> 'b list      ", vfun2 v_map)

let _ = Interpret.know ("take"     , "int -> 'a list -> 'a list             ", vfun2 v_take)
let _ = Interpret.know ("drop"     , "int -> 'a list -> 'a list             ", vfun2 v_drop)

let _ = Interpret.know ("takewhile", "('a -> bool) -> 'a list -> 'a list    ", vfun2 v_takewhile)
let _ = Interpret.know ("dropwhile", "('a -> bool) -> 'a list -> 'a list    ", vfun2 v_dropwhile)

let _ = Interpret.know ("zip"      , "'a list -> 'b list -> ('a*'b) list    ", vfun2 v_zip)
let _ = Interpret.know ("unzip"    , "('a*'b) list -> 'a list * 'b list     ", vfun v_unzip)

let _ = Interpret.know ("filter"   , "('a -> bool) -> 'a list -> 'a list    ", vfun2 v_filter)

let _ = Interpret.know ("exists"   , "('a -> bool) -> 'a list -> bool       ", vfun2 v_exists)
let _ = Interpret.know ("forall"   , "('a -> bool) -> 'a list -> bool       ", vfun2 v_forall)

let _ = Interpret.know ("foldl"    , "('a -> 'b -> 'a) -> 'a -> 'b list -> 'a", vfun3 v_foldl)
let _ = Interpret.know ("foldr"    , "('a -> 'b -> 'b) -> 'b -> 'a list -> 'b", vfun3 v_foldr)

let _ = Interpret.know ("concat"   , "'a list list -> 'a list                ", vfun v_concat )

let v_tabulate n f =
  let n = intv n in
  let f = funv f in
  let a = Array.init n (f <.> vint) in
  vlist (Array.to_list a)

let v_const a b = a
  
let _ = Interpret.know ("tabulate", "int -> (int -> 'a) -> 'a list"    , vfun2 v_tabulate)
let _ = Interpret.know ("const"   , "'a -> 'b -> 'a"                   , vfun2 v_const)

let v_sort vs = vlist (List.sort (fun a b -> ~- (Pervasives.compare a b)) (listv vs))
let _ = Interpret.know ("sort"    , "'a list -> 'a list"                , vfun v_sort)

let _ = Interpret.know ("fst"     , "'a*'b -> 'a"                       , vfun (Pervasives.fst <.> pairv))
let _ = Interpret.know ("snd"     , "'a*'b -> 'b"                       , vfun (Pervasives.snd <.> pairv))

let _ = Interpret.know ("randbit",  "unit -> bit"                       , vfun (vbit <.> (fun b -> if b then 1 else 0) <.> Random.bool <.> unitv))
let _ = Interpret.know ("randbits", "int -> bit list"                   , vfun v_randbits)

let v_max a b =
  let a = intv a in
  let b = intv b in
  vint (if a>b then a else b)
  
let v_min a b =
  let a = intv a in
  let b = intv b in
  vint (if a<b then a else b)

let _ = Interpret.know ("max", "int -> int -> int", vfun2 v_max)
let _ = Interpret.know ("min", "int -> int -> int", vfun2 v_min)

let v_bitand i j = vint ((intv i) land (intv j))
let _ = Interpret.know ("bitand", "int -> int -> int", vfun2 v_bitand)

(* these have to be here because of subtyping bit<=int, damn it, and perhaps for efficiency *)

let v_bits2int bits = vint (List.fold_left (fun sum b -> sum*2+intv b) 0 (listv bits))
let v_int2bits i = let rec int2bits bs i = 
                     let b = vint (i mod 2) in
                     if i>1 then int2bits (b::bs) (i/2) else List.rev (b::bs)
                   in
                   vlist (int2bits [] (intv i))

let _ = Interpret.know ("bits2int", "bit list -> int", vfun v_bits2int)
let _ = Interpret.know ("int2bits", "int -> bit list", vfun v_int2bits)

let v_nth vs i = 
  try List.nth (listv vs) (intv i)
  with Failure _ -> raise (LibraryError (Printf.sprintf "nth %s %s" (string_of_value vs) (string_of_value i)))
let _ = Interpret.know ("nth", "'a list -> int -> 'a", vfun2 v_nth)

(* ********************* I/O ************************ *)

(* I'm ashamed to say that all these read_.. functions are hacked to deal with BBEdit's weird shell worksheet
   input mechanism: if the line they read starts with the prompt then they strip it off. Sorry.
 *)

let rec get_string s = 
  flush stdout; 
  let prompt = stringv s ^"? " in
  prerr_string prompt; flush stderr; 
  let input = Pervasives.read_line () in
  let plength = String.length prompt in
  let ilength = String.length input in
  if plength<ilength && Stringutils.starts_with input prompt 
  then String.sub input plength (ilength - plength)
  else input
  
let rec read_int s = try vint (int_of_string (get_string s)) with Failure _ -> print_endline "pardon?"; read_int s
let _ = Interpret.know ("read_int", "string -> int"                     , vfun read_int)

let rec read_string s = vstring (get_string s) 
let _ = Interpret.know ("read_string", "string -> string"               , vfun read_string)

let rec read_alternative prompt sep alts =
  let assoc = List.map pairv (listv alts) in
  let promptstring = Printf.sprintf "%s (%s)" 
                                    (stringv prompt) 
                                    (String.concat (stringv sep) (List.map (stringv <.> fst) assoc)) 
  in
  let s = read_string (vstring promptstring) in
  try List.assoc s assoc
  with Not_found -> print_endline "pardon?"; read_alternative prompt sep alts

let _ = Interpret.know ("read_alternative", "string -> string -> (string*'a) list -> 'a", vfun3 read_alternative)
  
let read_bool prompt y n = read_alternative prompt (vstring "/") (vlist [vpair (y,vbool true); vpair (n,vbool false)])
let _ = Interpret.know ("read_bool", "string -> string -> string -> bool", vfun3 read_bool)

exception Abandon of string

let abandon ss = raise (Abandon (String.concat "" (List.map stringv (listv ss))))
let _ = Interpret.know ("abandon", "string list -> 'a", vfun abandon)


let print_string s = vunit (Pervasives.print_string (stringv s); flush stdout)
let print_qbit q   = print_string (vstring (Qsim.string_of_qval (Qsim.qval (qbitv q))))  
                                        
let _ = Interpret.know ("print_string" , "string -> unit"       , vfun (print_string))
let _ = Interpret.know ("print_strings", "string list -> unit"  , vfun (v_iter (vfun print_string)))
let _ = Interpret.know ("print_qbit"   , "qbit -> unit"         , vfun print_qbit)

let _ = Interpret.know ("show", "'a -> string", vfun (vstring <.> string_of_value))

(* ******************** cheats ********************* *)

(* selecting bits from a sequence length n with probability p:
   how large must n be to guarantee that we get k bits?
   Well: we need to know how many standard deviations sigma you want to
   allow: 6 sigma is plenty. Then 
   
     sigma = sqrt (n*p*(1-p))
   
   The mean number that will be picked is n*p; pick n so that the mean is
   s sigmas larger than the number you need:
   
     k = n*p - s*sigma
     
   which is a quadratic in sqrt n, with a=p, b=-s*sqrt(p*(1-p)), c=-k.
   Put q=p*(1-p) and we have
   
     sqrt n = (s*sqrt q + sqrt(s^2*q+4*k*p))/2*p
     
   We give p as a rational i/j
 *)
let min_qbits (k:int) (p:int*int) (s:int) : int =
  let i,j = p in
  let f_p = float i /. float j in
  let f_q = f_p *. (1.0 -. f_p) in
  let f_s = float s in
  let f_k = float k in
  let f_rootn = (f_s *. sqrt f_q +. sqrt((f_s *. f_s *. f_q) +. (4.0 *. f_k *. f_p))) /. (2.0 *. f_p) in
  truncate ((f_rootn *. f_rootn) +. 0.5)

let _min_qbits k p s =
  let i,j = pairv p in
  vint (min_qbits (intv k) (intv i, intv j) (intv s))
  
let _ = Interpret.know ("min_qbits", "int -> int*int -> int -> int", vfun3 _min_qbits)
