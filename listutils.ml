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

exception Zip

let zip xs ys = try List.combine xs ys with Invalid_argument _ -> raise Zip
let unzip = List.split

(* why don't we have (::)? *)
let cons x xs = x::xs
let null xs = match xs with [] -> true | _ -> false

let (<@>) xys x = List.assoc x xys
let (<@@>) xys x = List.assq x xys

let (<@?>) xys x = List.mem_assoc x xys
let (<@@?>) xys x = List.mem_assq x xys

let (<@->) xys x = List.remove_assoc x xys
let (<@@->) xys x = List.remove_assq x xys

let string_of_list fx sep xs = String.concat sep (List.map fx xs)

let bracketed_string_of_list fx xs = "[" ^ string_of_list fx ";" xs ^ "]"

let string_of_assoc fx fy colon semicolon xys = 
  String.concat semicolon (List.map (fun (x,y) -> fx x ^ colon ^ fy y) xys)

let numbered xs = Array.to_list (Array.mapi (fun i x -> i,x) (Array.of_list xs))
