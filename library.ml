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
open Interpret

(* ******************** built-in functions ********************* *)

(* This stuff is intended to be replaced by dynamically-loaded stuff,
   as soon as I can get round to understanding the mechanism.
 *)

let vfun2 f = vfun (fun a -> vfun (fun b -> f a b))
let vfun3 f = vfun (fun a -> vfun (fun b -> vfun (fun c -> f a b c)))

let v_hd vs =
  let vs = listv vs in
  try List.hd vs with _ -> raise (Error (dummy_spos, "hd []"))

let v_tl vs =
  let vs = listv vs in
  try vlist (List.tl vs) with _ -> raise (Error (dummy_spos, "tl []"))
  
let v_append xs ys =
  let xs = listv xs in
  let ys = listv ys in
  vlist (List.append xs ys)
  
let v_iter f xs =
  let f = funv f in
  let xs = listv xs in
  vunit (List.iter (fun v -> ignore (f v)) xs)

let v_map f xs =
  let f = funv f in
  let xs = listv xs in
  vlist (List.map f xs)

let v_take n xs =
  let n = intv n in
  let xs = listv xs in
  let rec take rs n xs =
    match n, xs with
    | 0, _
    | _, []     -> vlist (List.rev rs)
    | _, x::xs  -> take (x::rs) (n-1) xs
  in
  take [] n xs
  
let v_drop n xs =
  let n = intv n in
  let xs = listv xs in
  let rec drop n xs =
    match n, xs with
    | 0, _
    | _, []     -> vlist []
    | _, x::xs  -> drop (n-1) xs
  in
  drop n xs
  
let _ = Interpret.know ("hd"      , "'a list -> 'a"                     , vfun v_hd)
let _ = Interpret.know ("tl"      , "'a list -> 'a list"                , vfun v_tl)
let _ = Interpret.know ("rev"     , "'a list -> 'a list"                , vfun (vlist <.> List.rev <.> listv))
let _ = Interpret.know ("append"  , "'a list -> 'a list -> 'a list"     , vfun2 v_append)
let _ = Interpret.know ("iter"    , "('a -> unit) -> 'a list -> unit"   , vfun2 v_iter)
let _ = Interpret.know ("map"     , "('a -> 'b) -> 'a list -> 'b list"  , vfun2 v_map)
let _ = Interpret.know ("take"    , "int -> 'a list -> 'a list"         , vfun2 v_take)
let _ = Interpret.know ("drop"    , "int -> 'a list -> 'a list"         , vfun2 v_drop)
let _ = Interpret.know ("fst"     , "'a*'b -> 'a"                       , vfun (Pervasives.fst <.> pairv))
let _ = Interpret.know ("snd"     , "'a*'b -> 'b"                       , vfun (Pervasives.snd <.> pairv))

let read_int s = print_string ("\n" ^ s ^"? "); flush stdout; Pervasives.read_int ()
let _ = Interpret.know ("read_int", "string -> int"        , vfun (vint <.> read_int <.> stringv))

let read_string s = print_string ("\n" ^ s ^"? "); flush stdout; Pervasives.read_line ()
let _ = Interpret.know ("read_string", "string -> string"        , vfun (vstring <.> read_string <.> stringv))

exception Abandon of string

let abandon s = raise (Abandon s)
let _ = Interpret.know ("abandon", "string -> 'a", vfun (abandon <.> stringv))

let qbit_state q =  Printf.sprintf "%s:%s" (Qsim.string_of_qbit q) 
                                        (Qsim.string_of_qval (Qsim.qval q)) 
                                        
let _ = Interpret.know ("qbit_state", "qbit -> string"        , vfun (vstring <.> qbit_state <.> qbitv))

let print_string = vunit <.> Pervasives.print_string <.> stringv
let _ = Interpret.know ("print_string", "string -> unit"        , vfun (print_string))
let _ = Interpret.know ("print_strings", "string list -> unit"  , vfun (v_iter (vfun print_string)))

let _ = Interpret.know ("string_of_value", "'a -> string", vfun (vstring <.> string_of_value))
