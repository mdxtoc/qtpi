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
open Sourcepos
open Functionutils
open Listutils
open Tupleutils
open Name
open Number
open Vt
open Value
open Vmg

exception IntOverflow of string
exception FractionalInt of string
exception NegInt of string

(* We 'declare' library things by adding them to this list: name * type (as string) * value.
   No more run-time typing, so it's important to get that type right.
 *)

let knowns = (ref [] : (name * string * vt) list ref)

let know dec = knowns := dec :: !knowns

(* should this give an error if n is fractional? The purist in me says yes. 
   The pragmatist says just take the floor and forget it.
 *)
let mustbe_intv v = 
  let n = to_num v in
  (*if is_int n then*) 
    try int_of_num n with Z.Overflow -> raise (IntOverflow (string_of_num n))
  (*else raise (FractionalInt (string_of_value v))*)

(* ******************** basic gates ********************* *)

let _ = know ("I"     , "gate", of_gate g_I)
let _ = know ("X"     , "gate", of_gate g_X)
let _ = know ("Y"     , "gate", of_gate g_Y)
let _ = know ("Z"     , "gate", of_gate g_Z)

let _ = know ("H"     , "gate", of_gate g_H)
let _ = know ("Rz"    , "gate", of_gate g_Rz)
let _ = know ("Rx"    , "gate", of_gate g_Rx)

let _ = know ("phi"   , "num -> gate", qtpfun (of_gate <.> g_Phi <.> mustbe_intv))

let _ = know ("Cnot"  , "gate", of_gate g_Cnot)
let _ = know ("CNot"  , "gate", of_gate g_Cnot)
let _ = know ("CNOT"  , "gate", of_gate g_Cnot)
let _ = know ("CX"    , "gate", of_gate g_CX)
let _ = know ("CY"    , "gate", of_gate g_CY)
let _ = know ("CZ"    , "gate", of_gate g_CZ)

let _ = know ("Swap"  , "gate", of_gate g_Swap)
let _ = know ("SWAP"  , "gate", of_gate g_Swap)

let _ = know ("T"     , "gate", of_gate g_Toffoli)
let _ = know ("F"     , "gate", of_gate g_Fredkin)
let _ = know ("Cswap" , "gate", of_gate g_Fredkin)
let _ = know ("CSwap" , "gate", of_gate g_Fredkin)
let _ = know ("CSWAP" , "gate", of_gate g_Fredkin)

let _ = know ("sx_0"    , "sxnum", of_csnum Snum.c_0)
let _ = know ("sx_1"    , "sxnum", of_csnum Snum.c_1)
let _ = know ("sx_i"    , "sxnum", of_csnum Snum.c_i)
let _ = know ("sx_h"    , "sxnum", of_csnum Snum.c_h)
let _ = know ("sx_f"    , "sxnum", of_csnum Snum.c_f)
let _ = know ("sx_g"    , "sxnum", of_csnum Snum.c_g)

let v_makeC g =
  if gsize g<>z_2 then
    raise (LibraryError ("makeC " ^ string_of_gate g))
  else
    make_C g

let _ = know ("makeC", "gate -> gate", qtpfun (of_gate <.> v_makeC <.> to_gate))

(* ******************** lists ********************* *)

let v_hd vs =
  let vs = to_list vs in
  try List.hd vs with _ -> raise (LibraryError "hd []")

let v_tl vs =
  let vs = to_list vs in
  try of_list (List.tl vs) with _ -> raise (LibraryError "tl []")
  
let v_append xs ys =
  let xs = to_list xs in
  let ys = to_list ys in
  of_list (List.append xs ys)
  
let v_fxs cf vf v2cf f xs =
  let f = camlfun f in
  let xs = to_list xs in
  vf (cf (v2cf <.> f) xs)
;;

let v_iter = v_fxs List.iter of_unit ignore

let v_map = v_fxs List.map of_list id

let v_filter = v_fxs List.filter of_list to_bool

let v_exists = v_fxs List.exists of_bool to_bool

let v_forall = v_fxs List.for_all of_bool to_bool

let v_foldl f a xs = 
  let f = camlfun2 f in
  let xs = to_list xs in
  List.fold_left f a xs
  
let v_foldr f a xs = 
  let f = camlfun2 f in
  let xs = to_list xs in
  List.fold_right f xs a

let v_take n xs =
  let i = mustbe_intv n in
  let xs = to_list xs in
  of_list (Listutils.take i xs)
  
let v_takewhile p xs =
  let p = to_bool <.> camlfun p in
  let xs = to_list xs in
  of_list (Listutils.takewhile p xs)
  
let v_drop n xs =
  let i = mustbe_intv n in
  let xs = to_list xs in
  of_list (Listutils.drop i xs)

let rec v_dropwhile p xs =
  let p = to_bool <.> camlfun p in
  let xs = to_list xs in
  of_list (Listutils.dropwhile p xs)

let v_randbits n =
  let i = mustbe_intv n in
  let rec randbits i =
    if i=0 then [] 
    else (let b = Random.bool () in
          of_bit b::randbits (i-1)
         ) 
  in
  of_list (randbits i)

let v_zip xs ys = of_list (List.map hide_pair (mirazip (to_list xs) (to_list ys))) 

let v_unzip xys = let xs, ys = List.split (List.map reveal_pair (to_list xys)) in
                  hide_pair (of_list xs, of_list ys)

let v_concat xss = of_list (List.concat (List.map to_list (to_list xss)))

let _ = know ("length"   , "['a] -> num                        "  , qtpfun (hide_int <.> List.length <.> to_list))

let _ = know ("hd"       , "['a] -> 'a                         "  , qtpfun v_hd)
let _ = know ("tl"       , "['a] -> ['a]                    "     , qtpfun v_tl)

let _ = know ("rev"      , "['a] -> ['a]                    "     , qtpfun (of_list <.> List.rev <.> to_list))
let _ = know ("append"   , "['a] -> ['a] -> ['a]         "        , qtpfun2 v_append)

let _ = know ("iter"     , "('a -> ()) -> ['a] -> ()       "      , qtpfun2 v_iter)
let _ = know ("map"      , "('a -> 'b) -> ['a] -> ['b]      "     , qtpfun2 v_map)

let _ = know ("take"     , "num -> ['a] -> ['a]             "     , qtpfun2 v_take)
let _ = know ("drop"     , "num -> ['a] -> ['a]             "     , qtpfun2 v_drop)

let _ = know ("takewhile", "('a -> bool) -> ['a] -> ['a]    "     , qtpfun2 v_takewhile)
let _ = know ("dropwhile", "('a -> bool) -> ['a] -> ['a]    "     , qtpfun2 v_dropwhile)

let _ = know ("zip"      , "['a] -> ['b] -> [('a,'b)]    "        , qtpfun2 v_zip)
let _ = know ("unzip"    , "[('a,'b)] -> (['a], ['b])     "       , qtpfun v_unzip)

let _ = know ("mzip"     , "['a] -> ['b] -> [('a,'b)]    ", qtpfun2 (fun xs ys -> of_list (List.map hide_pair (mirazip (to_list xs) (to_list ys)))))
let _ = know ("mzip2"    , "['a] -> ['b] -> [('a,'b)]    ", qtpfun2 (fun xs ys -> of_list (List.map hide_pair (mirazip (to_list xs) (to_list ys)))))
let _ = know ("mzip3"    , "['a] -> ['b] -> ['c] -> [('a,'b,'c)]    "
                            , qtpfun3 (fun xs ys zs -> of_list (List.map hide_triple (mirazip3 (to_list xs) (to_list ys) (to_list zs)))))

let _ = know ("filter"   , "('a -> bool) -> ['a] -> ['a]    "     , qtpfun2 v_filter)

let _ = know ("exists"   , "('a -> bool) -> ['a] -> bool       "  , qtpfun2 v_exists)
let _ = know ("forall"   , "('a -> bool) -> ['a] -> bool       "  , qtpfun2 v_forall)

let _ = know ("foldl"    , "('a -> 'b -> 'a) -> 'a -> ['b] -> 'a" , qtpfun3 v_foldl)
let _ = know ("foldr"    , "('a -> 'b -> 'b) -> 'b -> ['a] -> 'b" , qtpfun3 v_foldr)

let _ = know ("concat"   , "[['a]] -> ['a]                "       , qtpfun v_concat )

let v_tabulate n f =
  let i = mustbe_intv n in
  let f = camlfun f in
  let a = Array.init i (f <.> hide_int) in
  of_list (Array.to_list a)

let v_const a b = a
  
let _ = know ("tabulate", "num -> (num -> 'a) -> ['a]"            , qtpfun2 v_tabulate)
let _ = know ("const"   , "'a -> '*b -> 'a"                       , qtpfun2 v_const)

(* 'compare' is now done in kompile_expr *)

let v_sort compare vs = of_list (List.sort (fun a b -> mustbe_intv ((camlfun2 compare) a b)) (to_list vs))
let _ = know ("sort"    , "(''a -> ''a -> num) -> [''a] -> [''a]" , qtpfun2 v_sort)

let _ = know ("fst"     , "('a,'b) -> 'a"                         , qtpfun (Stdlib.fst <.> reveal_pair))
let _ = know ("snd"     , "('a,'b) -> 'b"                         , qtpfun (Stdlib.snd <.> reveal_pair))

let _zeroes = ref z_0
let _ones = ref z_1

let vrandbit () = 
  let b = Random.bool () in
  if !Settings.checkrandombias then
    (if b then _ones := !_ones +: z_1 else _zeroes := !_zeroes +: z_1);
  b
  
let _ = know ("randbit",  "() -> bit"                             , qtpfun (of_bit <.> vrandbit <.> to_unit))
let _ = know ("randbits", "num -> [bit]"                          , qtpfun v_randbits)

let v_max a b =
  let a = to_num a in
  let b = to_num b in
  of_num (if a>/b then a else b)
  
let v_min a b =
  let a = to_num a in
  let b = to_num b in
  of_num (if a</b then a else b)

let _ = know ("max", "num -> num -> num", qtpfun2 v_max)
let _ = know ("min", "num -> num -> num", qtpfun2 v_min)

let v_bitand i j = 
  let i = to_num i in
  let j = to_num j in
  if not (is_int i) then raise (FractionalInt (string_of_num i));
  if not (is_int j) then raise (FractionalInt (string_of_num j));
  of_num (num_of_zint (Z.(land) (zint_of_num i) (zint_of_num j)))

let _ = know ("bitand", "num -> num -> num", qtpfun2 v_bitand)

(* these have to be here because of subtyping bit<=int, damn it, and perhaps for efficiency *)

(* let v_bits2num bits = 
     let zi = List.fold_left (fun sum b -> Z.(shift_left sum 1 + if to_bool b then one else zero)) Z.zero (to_list bits) in
     of_num (num_of_zint zi)
  
   let v_num2bits n = let rec num2bits bs zi = 
                        let q,b = Z.div_rem zi ztwo in
                        let b = of_bit Z.(equal b one) in
                        if not Z.(equal q zero) then num2bits (b::bs) q else List.rev (b::bs)
                      in
                      let n = to_num n in
                      if not (is_int n) then raise (FractionalInt (string_of_num n));
                      if not (n>=/zero) then raise (IntOverflow (string_of_num n));
                      of_list (num2bits [] (zint_of_num n))
 *)

(* little-endian: least-significant bit first *)
let v_num2bits n =
  let n = to_num n in
  if not (is_int n) then raise (FractionalInt (string_of_num n));
  if Q.sign n < 0 then raise (NegInt (string_of_num n));
  let s = Z.to_bits (Q.num n) in
  let cs = (ref [] : int list ref) in
  let ncs = String.length s - 1 in
  for i = 0 to ncs do cs := Char.code s.[i] :: !cs done; (* big-endian: first byte last in !cs *)
  let rec char2bits k bs byte =
    let b = of_bit ((byte land 1) = 1) in
    let byte = byte lsr 1 in
    if byte=k then List.rev (b::bs) else char2bits k (b::bs) byte
  in
  let rec cs2bits bits = function
    | [byte]      -> List.concat (List.rev (char2bits 0 [] byte::bits))
    | byte::bytes -> cs2bits (char2bits 1 [] (byte+256)::bits) bytes
    | []          -> [of_bit false]
  in
  of_list (cs2bits [] (List.rev (dropwhile (fun byte -> byte=0) !cs)))

(* also little-endian, to match v_num2bits *)
let v_bits2num bs =
  let rec bytevalue bs = (* little-endian *)
    let rec bv byte = function (* big-endian *)
      | []    -> byte
      | b::bs -> bv ((byte lsl 1)+(if to_bool b then 1 else 0)) bs
    in bv 0 (List.rev bs)
  in
  let rec listvalue bytes = function (* little-endian *)
    | [] -> List.rev bytes 
    | bs -> listvalue (bytevalue (take 8 bs)::bytes) (drop 8 bs) 
  in
  let a = Array.of_list (listvalue [] (to_list bs)) in
  let s = String.init (Array.length a) (fun i -> Char.chr a.(i)) in
  let zn = Z.of_bits s in
  of_num (num_of_zint zn)

let _ = know ("bits2num", "[bit] -> num", qtpfun v_bits2num)
let _ = know ("num2bits", "num -> [bit]", qtpfun v_num2bits)

let v_nth vs n = 
  let i = mustbe_intv n in
  try List.nth (to_list vs) i
  with Failure _ -> 
    raise (LibraryError (Printf.sprintf "nth %s, list length %s" 
                            (string_of_int i)
                            (string_of_int (List.length (to_list vs)))
                        )
          )

let _ = know ("nth", "['a] -> num -> 'a", qtpfun2 v_nth)

(* ********************* numbers ************************ *)

let _ = know ("floor"  , "num -> num", qtpfun (of_num <.> Number.floor <.> to_num))
let _ = know ("ceiling", "num -> num", qtpfun (of_num <.> Number.ceiling <.> to_num))
let _ = know ("round"  , "num -> num", qtpfun (of_num <.> Number.round <.> to_num))

let _ = know ("sqrt"   , "num -> num", qtpfun (of_num <.> Q.of_float <.> sqrt <.> Q.to_float <.> to_num))
let _ = know ("pi"     , "num"       , of_num (Q.of_float (Float.pi))) 

(* ********************* gates, matrices ************************ *)
 
let v_tabulate_m m n f =
  let m = mustbe_intv m in
  let n = mustbe_intv n in
  let f = camlfun2 f in
  let ff i j = to_csnum (f ((of_num <.> num_of_int) i) ((of_num <.> num_of_int) j)) in
  of_matrix (maybe_sparse_m (init_dm m n ff))
 
let v_tabulate_diag_m n f =
  let n = mustbe_intv n in
  let f = camlfun f in
  of_matrix (init_diag_m (Z.of_int n) (to_csnum <.> f <.> of_num <.> num_of_zint))
 
let _ = know ("tabulate_m"  , "num -> num -> (num -> num -> sxnum) -> matrix", qtpfun3 v_tabulate_m)
let _ = know ("tabulate_diag_m"  , "num -> (num -> sxnum) -> matrix", qtpfun2 v_tabulate_diag_m)

let _ = know ("degate"  , "gate -> matrix", qtpfun (of_matrix <.> matrix_of_gate <.> to_gate))
let _ = know ("engate"  , "matrix -> gate", qtpfun (of_gate <.> Vmg.engate <.> to_matrix))

let _statistics_m mM =
  let assoc = Vmg.statistics_m (to_matrix mM) in
  of_list (List.map (fun (v,i) -> hide_pair (of_csnum v, of_num (num_of_zint i))) assoc)

let _statistics_snv nv =
  let assoc = Vmg.statistics_nv nv in
  of_list (List.map (fun (v,i) -> hide_pair (of_csnum v, of_num (num_of_zint i))) assoc)

let _ = know ("statistics_m", "matrix -> [(sxnum,num)]", qtpfun _statistics_m)
let _ = know ("statistics_k", "ket -> [(sxnum,num)]", qtpfun (_statistics_snv <.> to_ket))

(* ********************* I/O ************************ *)

(* I'm ashamed to say that all these read_.. functions are hacked to deal with BBEdit's weird shell worksheet
   input mechanism: if the line they read starts with the prompt then they strip it off. Sorry.
 *)

let rec get_string : vt -> string = fun s ->
  flush stdout; 
  let prompt = reveal_string s ^"? " in
  prerr_string prompt; flush stderr; 
  let input = Stdlib.read_line () in
  let plength = String.length prompt in
  let ilength = String.length input in
  if plength<ilength && Stringutils.starts_with input prompt 
  then String.sub input plength (ilength - plength)
  else input
  
let rec read_num : vt -> vt = fun s ->
  try let s = get_string s in
              of_num (num_of_string s) 
  with Failure _ 
     | Invalid_argument _ -> print_endline "pardon?"; read_num s

let _ = know ("read_num", "string -> num"                     , qtpfun read_num)

let rec read_string s = hide_string (get_string s) 
let _ = know ("read_string", "string -> string"               , qtpfun read_string)

let rec read_alternative prompt sep alts =
  let assoc = List.map reveal_pair (to_list alts) in
  let promptstring = Printf.sprintf "%s (%s)" 
                                    (reveal_string prompt) 
                                    (String.concat (reveal_string sep) (List.map (reveal_string <.> fst) assoc)) 
  in
  let s = read_string (hide_string promptstring) in
  try List.assoc s assoc
  with Not_found -> print_endline "pardon?"; read_alternative prompt sep alts

let _ = know ("read_alternative", "string -> string -> [(string,'a)] -> 'a", qtpfun3 read_alternative)
  
let read_bool prompt y n = read_alternative prompt (hide_string "/") (of_list [hide_pair (y,of_bool true); hide_pair (n,of_bool false)])
let _ = know ("read_bool", "string -> string -> string -> bool", qtpfun3 read_bool)

exception Abandon of string

let abandon ss = raise (Abandon (String.concat "" (List.map reveal_string (to_list ss))))
let _ = know ("abandon", "[string] -> '*a", qtpfun abandon) (* note classical result type ... *)


let print_string s = of_unit (Stdlib.print_string (reveal_string s); flush stdout)
let print_qbit q   = print_string (hide_string (Qsim.string_of_qval (Qsim.qval (to_qbit q))))  
                                        
let _ = know ("print_string" , "string -> ()"       , qtpfun (print_string))
let _ = know ("print_strings", "[string] -> ()"     , qtpfun (v_iter (qtpfun print_string)))
let _ = know ("print_qbit"   , "qbit -> ()"         , qtpfun print_qbit)    (* yup, that's a qbit argument *)

(* 'show' is now done in kompile_expr *)  

let _showf k n =    (* print n as float with k digits, rounded away from zero *)
  let k = mustbe_intv k in
  let n = to_num n in
  let r = (pow num_10 (-k)) */ half in
  let n = if Q.sign n < 0 then n-/r else n+/r in
  let n = Q.to_float n in
  hide_string (Printf.sprintf "%.*f" k n)

let _ = know ("showf", "num -> num -> string", qtpfun2 _showf)   
  
(* ********************* memoising, with an s ************************ *)

module OneMap = MyMap.Make (struct type t        = vt
                                   let compare   = Stdlib.compare (* can't be anything else *)
                                   let to_string = reveal_string
                            end
                           )

let _memofun f = OneMap.memofun id (camlfun f)
let _memorec f = OneMap.memorec id (camlfun2 f <.> qtpfun)

let _ = know ("memofun", "('a -> 'b) -> 'a -> 'b", qtpfun2 _memofun)
let _ = know ("memorec", "(('a -> 'b) -> 'a -> 'b) -> 'a -> 'b"           , qtpfun2 _memorec)
  
module TwoMap = MyMap.Make (struct type t        = vt*vt
                                   let compare   = Stdlib.compare (* ok not to be deepcompare *)
                                   let to_string = bracketed_string_of_pair reveal_string reveal_string
                            end
                           )

let _memofun2 f = curry2 (TwoMap.memofun id (uncurry2 (camlfun2 f)))

let _ = know ("memofun2", "('a -> 'b -> 'c) -> 'a -> 'b -> 'c"            , qtpfun3 _memofun2)
  
module ThreeMap = MyMap.Make (struct type t        = vt*vt*vt
                                     let compare   = Stdlib.compare (* ok not to be deepcompare *)
                                     let to_string = bracketed_string_of_triple reveal_string reveal_string reveal_string
                              end
                             )

let _memofun3 f = curry3 (ThreeMap.memofun id (uncurry3 (camlfun3 f)))
  
let _ = know ("memofun3", "('a -> 'b -> 'c -> 'd) -> 'a -> 'b -> 'c -> 'd", qtpfun4 _memofun3)

(* ********************* special qbit functions ************************ *)

let _qval q =
  let q = to_qbit q in
  let qs,v = Qsim.qval q in
  let qs',v' = Qsim.make_first qs v (Qsim.idx q qs) in
  let printit q qv = Printf.sprintf "%s:%s" (string_of_qbit q) (Qsim.string_of_qval (Qsim.qsort qv)) in
  match Qsim.try_split false qs' v' with
  | Some (q',v,_,_) when q=q' -> printit q ([q],v)
  | _                         -> printit q (qs,v)
  

let _qvals qs =
  let qs = to_qbits qs in
  let qv = Qsim.qval_of_qs qs in
  Printf.sprintf "%s:%s" (bracketed_string_of_list string_of_qbit qs) (Qsim.string_of_qval qv) (* oh the qsort ... *)
  
let _ = know ("qval" , "qbit  -> qstate", qtpfun (of_qstate <.> _qval))       (* yup, that's a qbit argument *)
let _ = know ("qvals", "qbits -> qstate", qtpfun (of_qstate <.> _qvals))      (* yup, that's a qbits argument *)
