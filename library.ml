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

let read_int () = flush stdout; print_string "\n?\n"; (* a bug in BBEdit shell script, so an extra \n *)
                  Pervasives.read_int ()
  
let _ = Interpret.know ("read_int", "unit -> int"        , vfun (vint <.> read_int <.> unitv))
