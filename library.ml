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

open Functionutils
open Interpret

(* ******************** built-in functions ********************* *)

(* This stuff is intended to be replaced by dynamically-loaded stuff,
   as soon as I can get round to understanding the mechanism.
 *)
let _ = Interpret.know ("hd"      , "'a list -> 'a"      , vfun (List.hd <.> listv))
let _ = Interpret.know ("tl"      , "'a list -> 'a list" , vfun (vlist <.> List.tl <.> listv))
let _ = Interpret.know ("fst"     , "'a*'b -> 'a"        , vfun (Pervasives.fst <.> pairv))
let _ = Interpret.know ("snd"     , "'a*'b -> 'b"        , vfun (Pervasives.snd <.> pairv))

let read_int s = print_string ("\n" ^ s ^"? "); flush stdout; Pervasives.read_int ()
let _ = Interpret.know ("read_int", "string -> int"        , vfun (vint <.> read_int <.> stringv))

let read_string s = print_string ("\n" ^ s ^"? "); flush stdout; Pervasives.read_line ()
let _ = Interpret.know ("read_string", "string -> string"        , vfun (vstring <.> read_string <.> stringv))

exception Abandon of string

let abandon s = raise (Abandon s)
let _ = Interpret.know ("abandon", "string -> 'a", vfun (abandon <.> stringv))

