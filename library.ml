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
                  with Invalid_argument _ -> raise (LibraryError (Printf.sprintf "zip %s %s" 
                                                                                 (bracketed_string_of_list string_of_value (listv xs))
                                                                                 (bracketed_string_of_list string_of_value (listv ys))
                                                          )
                                                   )

exception Abandon of string

let v_unzip xys = let xs, ys = List.split (List.map pairv (listv xys)) in
                  vpair (vlist xs, vlist ys)

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

let v_tabulate n f =
  let n = intv n in
  let f = funv f in
  let a = Array.init n (f <.> vint) in
  vlist (Array.to_list a)

let v_const a b = a
  
let _ = Interpret.know ("tabulate", "int -> (int -> 'a) -> 'a list"    , vfun2 v_tabulate)
let _ = Interpret.know ("const"   , "'a -> 'b -> 'a"                   , vfun2 v_const)

let _ = Interpret.know ("fst"     , "'a*'b -> 'a"                       , vfun (Pervasives.fst <.> pairv))
let _ = Interpret.know ("snd"     , "'a*'b -> 'b"                       , vfun (Pervasives.snd <.> pairv))

let _ = Interpret.know ("randbit",  "unit -> bit"                       , vfun (vbit <.> (fun b -> if b then 1 else 0) <.> Random.bool <.> unitv))
let _ = Interpret.know ("randbits", "int -> bit list"                   , vfun v_randbits)

let read_int s = flush stdout; prerr_string (s ^"? "); flush stderr; Pervasives.read_int ()
let _ = Interpret.know ("read_int", "string -> int"                     , vfun (vint <.> read_int <.> stringv))

let read_string s = flush stdout; prerr_string (s ^"? "); flush stderr; Pervasives.read_line ()
let _ = Interpret.know ("read_string", "string -> string"               , vfun (vstring <.> read_string <.> stringv))

let read_bool prompt y n =
  let prompt = stringv prompt in
  let y = stringv y in
  let n = stringv n in
  let s = read_string (Printf.sprintf "%s (%s/%s)" prompt y n) in 
  if s = y then vbool true else
  if s = n then vbool false else
  raise (Abandon (Printf.sprintf "read_bool \"%s\" saw %s; should have been %s or %s" prompt s y n))
let _ = Interpret.know ("read_bool", "string -> string -> string -> bool", vfun3 read_bool)

let abandon s = raise (Abandon s)
let _ = Interpret.know ("abandon", "string -> 'a", vfun (abandon <.> stringv))


let print_string s = vunit (Pervasives.print_string (stringv s); flush stdout)
let print_qbit q   = print_string (vstring (Qsim.string_of_qval (Qsim.qval (qbitv q))))  
                                        
let _ = Interpret.know ("print_string" , "string -> unit"       , vfun (print_string))
let _ = Interpret.know ("print_strings", "string list -> unit"  , vfun (v_iter (vfun print_string)))
let _ = Interpret.know ("print_qbit"   , "qbit -> unit"         , vfun print_qbit)

let _ = Interpret.know ("string_of_value", "'a -> string", vfun (vstring <.> string_of_value))
