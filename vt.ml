(*
    Copyright (C) 2018-2020 Richard Bornat
     
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

(* I make heavy use of Obj.magic at run time. Type vt is a place holder *)
(* to make show and compare -- and <, <=, >, >= -- work at all, we use the compile-time
   type
 *)

type vt = int (* but this is hidden by vt.mli *)

let string_of_vt : vt -> string = fun _ -> "?<runtime value>"

type rtenv = vt array
