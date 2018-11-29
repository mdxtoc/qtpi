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
open Number

(* ******************** built-in functions ********************* *)

(* This stuff is intended to be replaced by dynamically-loaded stuff,
   as soon as I can get round to understanding the mechanism.
 *)

let vfun2 f = vfun (fun a -> vfun (fun b -> f a b))
let vfun3 f = vfun (fun a -> vfun (fun b -> vfun (fun c -> f a b c)))

let funv2 f = funv <.> funv f

(* should this give an error if n is fractional? The purist in me says yes. 
   The pragmatist says just take the floor and forget it.
 *)
let mustbe_intv v = 
  let n = numv v in
  (*if is_int n then*) 
    try int_of_num n with Z.Overflow -> raise (IntOverflow (string_of_value v))
  (*else raise (FractionalInt (string_of_value v))*)

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
  let i = mustbe_intv n in
  let xs = listv xs in
  vlist (Listutils.take i xs)
  
let v_takewhile p xs =
  let p = boolv <.> funv p in
  let xs = listv xs in
  vlist (Listutils.takewhile p xs)
  
let v_drop n xs =
  let i = mustbe_intv n in
  let xs = listv xs in
  vlist (Listutils.drop i xs)

let rec v_dropwhile p xs =
  let p = boolv <.> funv p in
  let xs = listv xs in
  vlist (Listutils.dropwhile p xs)

let v_randbits n =
  let i = mustbe_intv n in
  let rec randbits i =
    if i=0 then [] 
    else (let b = Random.bool () in
          vbit b::randbits (i-1)
         ) 
  in
  vlist (randbits i)

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

let _ = Interpret.know ("length"   , "'a list -> num                        ", vfun (vint <.> List.length <.> listv))

let _ = Interpret.know ("hd"       , "'a list -> 'a                         ", vfun v_hd)
let _ = Interpret.know ("tl"       , "'a list -> 'a list                    ", vfun v_tl)

let _ = Interpret.know ("rev"      , "'a list -> 'a list                    ", vfun (vlist <.> List.rev <.> listv))
let _ = Interpret.know ("append"   , "'a list -> 'a list -> 'a list         ", vfun2 v_append)

let _ = Interpret.know ("iter"     , "('a -> unit) -> 'a list -> unit       ", vfun2 v_iter)
let _ = Interpret.know ("map"      , "('a -> 'b) -> 'a list -> 'b list      ", vfun2 v_map)

let _ = Interpret.know ("take"     , "num -> 'a list -> 'a list             ", vfun2 v_take)
let _ = Interpret.know ("drop"     , "num -> 'a list -> 'a list             ", vfun2 v_drop)

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
  let i = mustbe_intv n in
  let f = funv f in
  let a = Array.init i (f <.> vint) in
  vlist (Array.to_list a)

let v_const a b = a
  
let _ = Interpret.know ("tabulate", "num -> (num -> 'a) -> 'a list"    , vfun2 v_tabulate)
let _ = Interpret.know ("const"   , "'a -> 'b -> 'a"                   , vfun2 v_const)

let v_sort vs = vlist (List.sort (fun a b -> ~- (Pervasives.compare a b)) (listv vs))
let _ = Interpret.know ("sort"    , "'a list -> 'a list"                , vfun v_sort)

let _ = Interpret.know ("fst"     , "'a*'b -> 'a"                       , vfun (Pervasives.fst <.> pairv))
let _ = Interpret.know ("snd"     , "'a*'b -> 'b"                       , vfun (Pervasives.snd <.> pairv))

let _ = Interpret.know ("randbit",  "unit -> bit"                       , vfun (vbit <.> Random.bool <.> unitv))
let _ = Interpret.know ("randbits", "num -> bit list"                   , vfun v_randbits)

let v_max a b =
  let a = numv a in
  let b = numv b in
  VNum (if a>/b then a else b)
  
let v_min a b =
  let a = numv a in
  let b = numv b in
  VNum (if a</b then a else b)

let _ = Interpret.know ("max", "num -> num -> num", vfun2 v_max)
let _ = Interpret.know ("min", "num -> num -> num", vfun2 v_min)

let v_bitand i j = 
  let i = numv i in
  let j = numv j in
  if not (is_int i) then raise (FractionalInt (string_of_num i));
  if not (is_int j) then raise (FractionalInt (string_of_num j));
  VNum (num_of_zint (Z.(land) (zint_of_num i) (zint_of_num j)))

let _ = Interpret.know ("bitand", "num -> num -> num", vfun2 v_bitand)

(* these have to be here because of subtyping bit<=int, damn it, and perhaps for efficiency *)

let v_bits2num bits = 
  let zi = List.fold_left (fun sum b -> Z.(shift_left sum 1 + if bitv b then one else zero)) Z.zero (listv bits) in
  vnum (num_of_zint zi)
  
let v_num2bits n = let rec num2bits bs zi = 
                     let q,b = Z.div_rem zi ztwo in
                     let b = vbit Z.(b=one) in
                     if not Z.(q=zero) then num2bits (b::bs) q else List.rev (b::bs)
                   in
                   let n = numv n in
                   if not (is_int n) then raise (FractionalInt (string_of_num n));
                   if not (n>=/zero) then raise (IntOverflow (string_of_num n));
                   vlist (num2bits [] (zint_of_num n))

let _ = Interpret.know ("bits2num", "bit list -> num", vfun v_bits2num)
let _ = Interpret.know ("num2bits", "num -> bit list", vfun v_num2bits)

let v_nth vs n = 
  let i = mustbe_intv n in
  try List.nth (listv vs) i
  with Failure _ -> raise (LibraryError (Printf.sprintf "nth %s %s" (string_of_value vs) (string_of_int i)))
let _ = Interpret.know ("nth", "'a list -> num -> 'a", vfun2 v_nth)

(* ********************* numbers ************************ *)

let _ = Interpret.know ("floor"  , "num -> num", vfun (vnum <.> Number.floor <.> numv))
let _ = Interpret.know ("ceiling", "num -> num", vfun (vnum <.> Number.ceiling <.> numv))
let _ = Interpret.know ("round"  , "num -> num", vfun (vnum <.> Number.round <.> numv))

let _ = Interpret.know ("sqrt"   , "num -> num", vfun (vnum <.> Q.of_float <.> sqrt <.> Q.to_float <.> numv))

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
  
let rec read_num s = try VNum (num_of_string (get_string s)) with Failure _ -> print_endline "pardon?"; read_num s
let _ = Interpret.know ("read_num", "string -> num"                     , vfun read_num)

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
let _ = Interpret.know ("abandon", "string list -> 'a", vfun abandon) (* note classical result type ... *)


let print_string s = vunit (Pervasives.print_string (stringv s); flush stdout)
let print_qbit q   = print_string (vstring (Qsim.string_of_qval (Qsim.qval (qbitv q))))  
                                        
let _ = Interpret.know ("print_string" , "string -> unit"       , vfun (print_string))
let _ = Interpret.know ("print_strings", "string list -> unit"  , vfun (v_iter (vfun print_string)))
let _ = Interpret.know ("print_qbit"   , "qbit -> unit"         , vfun print_qbit)

let _show = function VQbit   _  -> "<qbit>"
            |        VQstate _  -> "<qstate>"
            |        VFun    _  -> "<function>"
            |        VChan    _ -> "<channel>"
            |        VProcess _ -> "<process>"
            |        v          -> string_of_value v

let _ = Interpret.know ("show", "''a -> string", vfun (vstring <.> _show))   (* yup, it's an equality type *)

let _showf k n =    (* print n as float with k digits, rounded away from zero *)
  let k = mustbe_intv k in
  let n = numv n in
  let r = (pow ten (-k)) */ half in
  let n = if Q.sign n < 0 then n-/r else n+/r in
  let n = Q.to_float n in
  vstring (Printf.sprintf "%.*f" k n)

let _ = Interpret.know ("showf", "num -> num -> string", vfun2 _showf)   
  
let _qval q =
  let q = qbitv q in
  Printf.sprintf "%s:%s" (Qsim.string_of_qbit q) (Qsim.string_of_qval (Qsim.qval q))
  
let _ = Interpret.know ("qval", "qbit -> qstate", vfun (vqstate <.> _qval))     (*yup, that's a qbit argument *)
