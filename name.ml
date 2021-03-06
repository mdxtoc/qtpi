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
open Sourcepos

type name = string 

let string_of_name n = n

module OrderedName = struct type t = name let compare = Stdlib.compare let to_string = string_of_name end
module NameSet = MySet.Make(OrderedName)
let addname = NameSet.add
let addnames = revargs (List.fold_left (revargs addname))
let memname = NameSet.mem
let subtractname = NameSet.remove
let subtractnames = revargs (List.fold_left (revargs subtractname)) 

module NameMap = MyMap.Make (OrderedName)
