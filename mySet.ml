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

module type OrderedType = sig
  include Set.OrderedType
  val to_string : t -> string
end

module type S = sig
  include Set.S
  val of_list   : elt list -> t
  val to_string : t -> string
  val map       : (elt -> elt) -> t -> t
end

module Make (Ord : OrderedType) = struct
  include Set.Make (struct type t = Ord.t let compare = Ord.compare end)
  
  let of_list elts = 
    List.fold_left (fun set elt -> add elt set) empty elts
    
  let to_string set =
    Printf.sprintf "{%s}" (Listutils.string_of_list Ord.to_string "," (elements set))
    
  let map f =
    of_list <.> List.map f <.> elements
end
