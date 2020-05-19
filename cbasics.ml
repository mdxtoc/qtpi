(*
    Copyright (C) 2018-20 Richard Bornat
     
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

open Vt

type cexpr = rtenv -> (vt -> unit) -> unit

type cfun = vt -> (vt -> unit) -> unit

let string_of_cexpr : cexpr -> string = fun _ -> "<cexpr>"

type 'a cpattern = rtenv -> vt -> 'a

let string_of_cpattern : 'a cpattern -> string = fun _ -> "<cpattern>"
let short_string_of_cpattern : 'a cpattern -> string = fun _ -> "<cpattern>"
