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

module type HashedType = sig
  include Hashtbl.HashedType
  val to_string : t -> string
end

module type S = sig
  include Hashtbl.S
  (* val to_assoc  : 'a t -> (key * 'a) list
     val of_assoc  : (key * 'a) list ->'a  t *)
  val to_string : ('a -> string) -> 'a t -> string
  (* val mymap     : ((key * 'a) -> 'b) -> ('b list -> 'c) -> 'a t -> 'c
     val mymerge   : ('a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
  val memofun   : 'a t -> (key -> 'a) -> key -> 'a
  (* val vmemofun  : bool -> string -> ('b -> string) -> ('a -> string) -> 
                    ('b -> key) -> ('b -> 'a) -> 'b -> 'a
     val memorec   : ('b -> key) -> (('b -> 'a) -> 'b -> 'a) -> 'b -> 'a
     val vmemorec  : bool -> string -> ('b -> string) -> ('a -> string) -> 
                    ('b -> key) -> (('b -> 'a) -> 'b -> 'a) -> 'b -> 'a *)
end

module Make (H : HashedType) = struct
  include Hashtbl.Make (struct type t = H.t let equal = H.equal let hash = H.hash end)
      
  let to_string string_of_target table =
    let keys = to_seq_keys table in
    let values = to_seq_values table in
    let realise s = List.rev (Seq.fold_left (fun xs x -> x::xs) [] s) in
    let pairs = Listutils.zip (realise keys) (realise values) in
    Printf.sprintf "{%s}" (Listutils.string_of_assoc H.to_string string_of_target "->" ";" pairs)
    
  let memofun table newf =
    let lookup x =
      try find table x 
      with Not_found -> (let y = newf x in
                         add table x y;
                         y
                        )
    in
    lookup
end
