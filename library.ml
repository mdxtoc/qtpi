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
open Tupleutils
open Interpret
open Number
open Value
open Vmg

(* should this give an error if n is fractional? The purist in me says yes. 
   The pragmatist says just take the floor and forget it.
 *)
let mustbe_intv v = 
  let n = numv v in
  (*if is_int n then*) 
    try int_of_num n with Z.Overflow -> raise (IntOverflow (string_of_value v))
  (*else raise (FractionalInt (string_of_value v))*)

(* ******************** built-in functions ********************* *)

let vfun2 f = vfun (fun a -> vfun (fun b -> f a b))
let vfun3 f = vfun (fun a -> vfun (fun b -> vfun (fun c -> f a b c)))
let vfun4 f = vfun (fun a -> vfun (fun b -> vfun (fun c -> vfun (fun d -> f a b c d))))

let funv2 f = funv <.> funv f
let funv3 f = let f' a b c = funv (funv (funv f a) b) c in
              f'

(* ******************** basic gates ********************* *)

let _ = Interpret.know ("I"     , "gate", vgate g_I)
let _ = Interpret.know ("X"     , "gate", vgate g_X)
let _ = Interpret.know ("Y"     , "gate", vgate g_Y)
let _ = Interpret.know ("Z"     , "gate", vgate g_Z)

let _ = Interpret.know ("H"     , "gate", vgate g_H)
let _ = Interpret.know ("Rz"    , "gate", vgate g_Rz)
let _ = Interpret.know ("Rx"    , "gate", vgate g_Rx)

let _ = Interpret.know ("phi"   , "num -> gate", vfun (vgate <.> g_Phi <.> mustbe_intv))

let _ = Interpret.know ("Cnot"  , "gate", vgate g_Cnot)
let _ = Interpret.know ("CNot"  , "gate", vgate g_Cnot)
let _ = Interpret.know ("CNOT"  , "gate", vgate g_Cnot)
let _ = Interpret.know ("CX"    , "gate", vgate g_CX)
let _ = Interpret.know ("CY"    , "gate", vgate g_CY)
let _ = Interpret.know ("CZ"    , "gate", vgate g_CZ)

let _ = Interpret.know ("Swap"  , "gate", vgate g_Swap)
let _ = Interpret.know ("SWAP"  , "gate", vgate g_Swap)

let _ = Interpret.know ("T"     , "gate", vgate g_Toffoli)
let _ = Interpret.know ("F"     , "gate", vgate g_Fredkin)
let _ = Interpret.know ("Cswap" , "gate", vgate g_Fredkin)
let _ = Interpret.know ("CSwap" , "gate", vgate g_Fredkin)
let _ = Interpret.know ("CSWAP" , "gate", vgate g_Fredkin)

let v_groverU vs = groverU (List.map bitv vs)

let _ = Interpret.know ("groverG", "num -> gate"      , vfun (vgate <.> groverG <.> mustbe_intv))
let _ = Interpret.know ("groverU", "[bit] -> gate"    , vfun (vgate <.> groverU <.> (List.map bitv) <.> listv))

let _ = Interpret.know ("dagger_g", "gate -> gate"    , vfun (vgate <.> Vmg.dagger_g <.> gatev))
let _ = Interpret.know ("dagger_m", "matrix -> matrix", vfun (vmatrix <.> Vmg.dagger_m <.> matrixv))

let _ = Interpret.know ("sx_0"    , "sxnum", vsxnum Snum.c_0)
let _ = Interpret.know ("sx_1"    , "sxnum", vsxnum Snum.c_1)
let _ = Interpret.know ("sx_i"    , "sxnum", vsxnum Snum.c_i)
let _ = Interpret.know ("sx_h"    , "sxnum", vsxnum Snum.c_h)
let _ = Interpret.know ("sx_f"    , "sxnum", vsxnum Snum.c_f)
let _ = Interpret.know ("sx_g"    , "sxnum", vsxnum Snum.c_g)

let v_makeC g =
  if gsize g<>2 then
    raise (LibraryError ("makeC " ^ string_of_gate g))
  else
    make_C g

let _ = Interpret.know ("makeC", "gate -> gate", vfun (vgate <.> v_makeC <.> gatev))

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

let _ = Interpret.know ("length"   , "['a] -> num                        "  , vfun (vint <.> List.length <.> listv))

let _ = Interpret.know ("hd"       , "['a] -> 'a                         "  , vfun v_hd)
let _ = Interpret.know ("tl"       , "['a] -> ['a]                    "     , vfun v_tl)

let _ = Interpret.know ("rev"      , "['a] -> ['a]                    "     , vfun (vlist <.> List.rev <.> listv))
let _ = Interpret.know ("append"   , "['a] -> ['a] -> ['a]         "        , vfun2 v_append)

let _ = Interpret.know ("iter"     , "('a -> ()) -> ['a] -> ()       "      , vfun2 v_iter)
let _ = Interpret.know ("map"      , "('a -> 'b) -> ['a] -> ['b]      "     , vfun2 v_map)

let _ = Interpret.know ("take"     , "num -> ['a] -> ['a]             "     , vfun2 v_take)
let _ = Interpret.know ("drop"     , "num -> ['a] -> ['a]             "     , vfun2 v_drop)

let _ = Interpret.know ("takewhile", "('a -> bool) -> ['a] -> ['a]    "     , vfun2 v_takewhile)
let _ = Interpret.know ("dropwhile", "('a -> bool) -> ['a] -> ['a]    "     , vfun2 v_dropwhile)

let _ = Interpret.know ("zip"      , "['a] -> ['b] -> [('a,'b)]    "        , vfun2 v_zip)
let _ = Interpret.know ("unzip"    , "[('a,'b)] -> (['a], ['b])     "       , vfun v_unzip)

let _ = Interpret.know ("mzip"     , "['a] -> ['b] -> [('a,'b)]    ", vfun2 (fun xs ys -> vlist (List.map vpair (mirazip (listv xs) (listv ys)))))
let _ = Interpret.know ("mzip2"    , "['a] -> ['b] -> [('a,'b)]    ", vfun2 (fun xs ys -> vlist (List.map vpair (mirazip (listv xs) (listv ys)))))
let _ = Interpret.know ("mzip3"    , "['a] -> ['b] -> ['c] -> [('a,'b,'c)]    "
                            , vfun3 (fun xs ys zs -> vlist (List.map vtriple (mirazip3 (listv xs) (listv ys) (listv zs)))))

let _ = Interpret.know ("filter"   , "('a -> bool) -> ['a] -> ['a]    "     , vfun2 v_filter)

let _ = Interpret.know ("exists"   , "('a -> bool) -> ['a] -> bool       "  , vfun2 v_exists)
let _ = Interpret.know ("forall"   , "('a -> bool) -> ['a] -> bool       "  , vfun2 v_forall)

let _ = Interpret.know ("foldl"    , "('a -> 'b -> 'a) -> 'a -> ['b] -> 'a" , vfun3 v_foldl)
let _ = Interpret.know ("foldr"    , "('a -> 'b -> 'b) -> 'b -> ['a] -> 'b" , vfun3 v_foldr)

let _ = Interpret.know ("concat"   , "[['a]] -> ['a]                "       , vfun v_concat )

let v_tabulate n f =
  let i = mustbe_intv n in
  let f = funv f in
  let a = Array.init i (f <.> vint) in
  vlist (Array.to_list a)

let v_const a b = a
  
let _ = Interpret.know ("tabulate", "num -> (num -> 'a) -> ['a]"            , vfun2 v_tabulate)
let _ = Interpret.know ("const"   , "'a -> '*b -> 'a"                       , vfun2 v_const)

let v_compare a b = vint (Interpret.deepcompare (a,b))
let _ = Interpret.know ("compare" , "'a -> 'a -> num", vfun2 v_compare)

let v_sort compare vs = vlist (List.sort (fun a b -> mustbe_intv ((funv2 compare) a b)) (listv vs))
let _ = Interpret.know ("sort"    , "(''a -> ''a -> num) -> [''a] -> [''a]" , vfun2 v_sort)

let _ = Interpret.know ("fst"     , "('a,'b) -> 'a"                         , vfun (Stdlib.fst <.> pairv))
let _ = Interpret.know ("snd"     , "('a,'b) -> 'b"                         , vfun (Stdlib.snd <.> pairv))

let _zeroes = ref zero
let _ones = ref zero

let vrandbit () = 
  let b = Random.bool () in
  if !Settings.checkrandombias then
    (if b then _ones := !_ones +/ one else _zeroes := !_zeroes +/ one);
  b
  
let _ = Interpret.know ("randbit",  "() -> bit"                             , vfun (vbit <.> vrandbit <.> unitv))
let _ = Interpret.know ("randbits", "num -> [bit]"                          , vfun v_randbits)

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

(* let v_bits2num bits = 
     let zi = List.fold_left (fun sum b -> Z.(shift_left sum 1 + if bitv b then one else zero)) Z.zero (listv bits) in
     vnum (num_of_zint zi)
  
   let v_num2bits n = let rec num2bits bs zi = 
                        let q,b = Z.div_rem zi ztwo in
                        let b = vbit Z.(equal b one) in
                        if not Z.(equal q zero) then num2bits (b::bs) q else List.rev (b::bs)
                      in
                      let n = numv n in
                      if not (is_int n) then raise (FractionalInt (string_of_num n));
                      if not (n>=/zero) then raise (IntOverflow (string_of_num n));
                      vlist (num2bits [] (zint_of_num n))
 *)

(* little-endian: least-significant bit first *)
let v_num2bits n =
  let n = numv n in
  if not (is_int n) then raise (FractionalInt (string_of_num n));
  if Q.sign n < 0 then raise (NegInt (string_of_num n));
  let s = Z.to_bits (Q.num n) in
  let cs = (ref [] : int list ref) in
  let ncs = String.length s - 1 in
  for i = 0 to ncs do cs := Char.code s.[i] :: !cs done; (* big-endian: first byte last in !cs *)
  let rec char2bits k bs byte =
    let b = vbit ((byte land 1) = 1) in
    let byte = byte lsr 1 in
    if byte=k then List.rev (b::bs) else char2bits k (b::bs) byte
  in
  let rec cs2bits bits = function
    | [byte]      -> List.concat (List.rev (char2bits 0 [] byte::bits))
    | byte::bytes -> cs2bits (char2bits 1 [] (byte+256)::bits) bytes
    | []          -> [vbit false]
  in
  vlist (cs2bits [] (List.rev (dropwhile (fun byte -> byte=0) !cs)))

(* also little-endian, to match v_num2bits *)
let v_bits2num bs =
  let rec bytevalue bs = (* little-endian *)
    let rec bv byte = function (* big-endian *)
      | []    -> byte
      | b::bs -> bv ((byte lsl 1)+(if bitv b then 1 else 0)) bs
    in bv 0 (List.rev bs)
  in
  let rec listvalue bytes = function (* little-endian *)
    | [] -> List.rev bytes 
    | bs -> listvalue (bytevalue (take 8 bs)::bytes) (drop 8 bs) 
  in
  let a = Array.of_list (listvalue [] (listv bs)) in
  let s = String.init (Array.length a) (fun i -> Char.chr a.(i)) in
  let zn = Z.of_bits s in
  vnum (num_of_zint zn)

let _ = Interpret.know ("bits2num", "[bit] -> num", vfun v_bits2num)
let _ = Interpret.know ("num2bits", "num -> [bit]", vfun v_num2bits)

let v_nth vs n = 
  let i = mustbe_intv n in
  try List.nth (listv vs) i
  with Failure _ -> raise (LibraryError (Printf.sprintf "nth %s %s" (string_of_value vs) (string_of_int i)))
let _ = Interpret.know ("nth", "['a] -> num -> 'a", vfun2 v_nth)

(* ********************* numbers ************************ *)

let _ = Interpret.know ("floor"  , "num -> num", vfun (vnum <.> Number.floor <.> numv))
let _ = Interpret.know ("ceiling", "num -> num", vfun (vnum <.> Number.ceiling <.> numv))
let _ = Interpret.know ("round"  , "num -> num", vfun (vnum <.> Number.round <.> numv))

let _ = Interpret.know ("sqrt"   , "num -> num", vfun (vnum <.> Q.of_float <.> sqrt <.> Q.to_float <.> numv))
let _ = Interpret.know ("pi"     , "num"       , vnum (Q.of_float (Float.pi))) 

(* ********************* gates, matrices ************************ *)
 
let _ = Interpret.know ("degate"  , "gate -> matrix", vfun (vmatrix <.> matrix_of_gate <.> gatev))
let _ = Interpret.know ("engate"  , "matrix -> gate", vfun (vgate <.> Vmg.engate <.> matrixv))

(* ********************* I/O ************************ *)

(* I'm ashamed to say that all these read_.. functions are hacked to deal with BBEdit's weird shell worksheet
   input mechanism: if the line they read starts with the prompt then they strip it off. Sorry.
 *)

let rec get_string s = 
  flush stdout; 
  let prompt = stringv s ^"? " in
  prerr_string prompt; flush stderr; 
  let input = Stdlib.read_line () in
  let plength = String.length prompt in
  let ilength = String.length input in
  if plength<ilength && Stringutils.starts_with input prompt 
  then String.sub input plength (ilength - plength)
  else input
  
let rec read_num s = try VNum (num_of_string (get_string s)) with Failure _ 
                                                                | Invalid_argument _ -> print_endline "pardon?"; read_num s
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

let _ = Interpret.know ("read_alternative", "string -> string -> [(string,'a)] -> 'a", vfun3 read_alternative)
  
let read_bool prompt y n = read_alternative prompt (vstring "/") (vlist [vpair (y,vbool true); vpair (n,vbool false)])
let _ = Interpret.know ("read_bool", "string -> string -> string -> bool", vfun3 read_bool)

exception Abandon of string

let abandon ss = raise (Abandon (String.concat "" (List.map stringv (listv ss))))
let _ = Interpret.know ("abandon", "[string] -> '*a", vfun abandon) (* note classical result type ... *)


let print_string s = vunit (Stdlib.print_string (stringv s); flush stdout)
let print_qbit q   = print_string (vstring (Qsim.string_of_qval (Qsim.qval (qbitv q))))  
                                        
let _ = Interpret.know ("print_string" , "string -> ()"       , vfun (print_string))
let _ = Interpret.know ("print_strings", "[string] -> ()"  , vfun (v_iter (vfun print_string)))
let _ = Interpret.know ("print_qbit"   , "qbit -> ()"         , vfun print_qbit)

let _show v = 
  let optf = function VQbit   _  -> Some "<qbit>"
             |        VQstate _  -> Some "<qstate>"
             |        VFun    _  -> Some "<function>"
             |        VChan    _ -> Some "<channel>"
             |        VProcess _ -> Some "<process>"
             |        _          -> None
  in
  so_value optf v
  
let _ = Interpret.know ("show", "'*a -> string", vfun (vstring <.> _show))   (* yup, it's a non-classical argument *)

let _showf k n =    (* print n as float with k digits, rounded away from zero *)
  let k = mustbe_intv k in
  let n = numv n in
  let r = (pow ten (-k)) */ half in
  let n = if Q.sign n < 0 then n-/r else n+/r in
  let n = Q.to_float n in
  vstring (Printf.sprintf "%.*f" k n)

let _ = Interpret.know ("showf", "num -> num -> string", vfun2 _showf)   
  
(* ********************* memoising, with an s ************************ *)

module OneMap = MyMap.Make (struct type t        = value
                                   let compare   = Stdlib.compare (* ok not to be deepcompare *)
                                   let to_string = string_of_value
                            end
                           )

let _memofun f = OneMap.memofun id (funv f)
let _memorec f = OneMap.memorec id (funv2 f <.> vfun)

let _ = Interpret.know ("memofun", "('a -> 'b) -> 'a -> 'b", vfun2 _memofun)
let _ = Interpret.know ("memorec", "(('a -> 'b) -> 'a -> 'b) -> 'a -> 'b"           , vfun2 _memorec)
  
module TwoMap = MyMap.Make (struct type t        = value*value
                                   let compare   = Stdlib.compare (* ok not to be deepcompare *)
                                   let to_string = string_of_pair string_of_value string_of_value " " 
                            end
                           )

let _memofun2 f = curry2 (TwoMap.memofun id (uncurry2 (funv2 f)))

let _ = Interpret.know ("memofun2", "('a -> 'b -> 'c) -> 'a -> 'b -> 'c"            , vfun3 _memofun2)
  
module ThreeMap = MyMap.Make (struct type t        = value*value*value
                                     let compare   = Stdlib.compare (* ok not to be deepcompare *)
                                     let to_string = string_of_triple string_of_value string_of_value string_of_value " " 
                              end
                             )

let _memofun3 f = curry3 (ThreeMap.memofun id (uncurry3 (funv3 f)))
  
let _ = Interpret.know ("memofun3", "('a -> 'b -> 'c -> 'd) -> 'a -> 'b -> 'c -> 'd", vfun4 _memofun3)

(* ********************* special qbit functions ************************ *)

let _qval q =
  let q = qbitv q in
  let qv = Qsim.qval q in
  Printf.sprintf "%s:%s" (string_of_qbit q) (Qsim.string_of_qval (Qsim.qsort qv))
  
let _ = Interpret.know ("qval", "qbit -> qstate", vfun (vqstate <.> _qval))     (* yup, that's a qbit argument *)
