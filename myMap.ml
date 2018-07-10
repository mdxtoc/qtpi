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
    along with Qtpi; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
    (or look at http://www.gnu.org).
*)

open Functionutils

module type OrderedType = sig
  include Map.OrderedType
  val to_string : t -> string
end

module type S = sig
  include Map.S
  val to_assoc  : 'a t -> (key * 'a) list
  val of_assoc  : (key * 'a) list -> 'a  t
  val to_string : ('a -> string) -> 'a t -> string
  val mymap     : ((key * 'a) -> 'b) -> ('b list -> 'c) -> 'a t -> 'c
  val mymerge   : ('a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t
  val memofun   : ('b -> key) -> ('b -> 'a) -> 'b -> 'a
  val vmemofun  : bool -> string -> ('b -> string) -> ('a -> string) -> 
                    ('b -> key) -> ('b -> 'a) -> 'b -> 'a
  val memorec   : ('b -> key) -> (('b -> 'a) -> 'b -> 'a) -> 'b -> 'a
  val vmemorec  : bool -> string -> ('b -> string) -> ('a -> string) -> 
                    ('b -> key) -> (('b -> 'a) -> 'b -> 'a) -> 'b -> 'a
end

module Make (Ord : OrderedType) = struct
  include Map.Make (struct type t = Ord.t let compare = Ord.compare end)
  
  let to_assoc = bindings
  let of_assoc assoc = 
    List.fold_left (fun map (key,alpha) -> add key alpha map) empty assoc
    
  let to_string string_of_target map =
    Printf.sprintf "{%s}" (Listutils.string_of_assoc Ord.to_string string_of_target "->" ";" (bindings map))
    
  let mymap f output =
    output <.> List.map f <.> bindings

  let mymerge union m1 m2 =
    let ff _ opt1 opt2 =
      match opt1, opt2 with
      | Some v1, Some v2 -> Some (union v1 v2)
      | Some _ , None    -> opt1
      | None   , Some _  -> opt2
      | None   , None    -> None
    in
    merge ff m1 m2
    
  let memofun key_of newf =
    let table = ref empty in
    let lookup x =
      let key = key_of x in
      try find key !table
      with Not_found -> (let y = newf x in
                         table := add key y !table;
                         y
                        )
    in
    lookup

  let vmemofun verbose str string_of_alpha string_of_target key_of newf =
    if verbose then
      Printf.printf "\ninitialising vmemofun %s" str;
    let table = ref empty in
    let lookup x =
      let r = let key = key_of x in
              try find key !table
              with Not_found -> (let y = newf x in
                                 table := add key y !table;
                                 y
                                )
      in
      if verbose then
        Printf.printf "\nvmemofun.lookup %s %s -> %s" str (string_of_alpha x) (string_of_target r);
      r
    in
    lookup

  let memorec key_of newf =
    let table = ref empty in
    let rec lookup x =
      let key = key_of x in
      try find key !table
      with Not_found -> (let y = newf lookup x in
                         table := add key y !table;
                         y
                        )
    in
    lookup

  let vmemorec verbose str string_of_alpha string_of_target key_of newf =
    if verbose then
      Printf.printf "\ninitialising vmemofun %s" str;
    let table = ref empty in
    let rec lookup x =
      let r = let key = key_of x in
              try find key !table
              with Not_found -> (let y = newf lookup x in
                                 table := add key y !table;
                                 y
                                )
      in
      if verbose then
        Printf.printf "\nvmemorec.lookup %s %s -> %s" str (string_of_alpha x) (string_of_target r);
      r
    in
    lookup
end
