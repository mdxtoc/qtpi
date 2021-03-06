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

exception Disaster of string

(* type basisv =
     | BVzero
     | BVone
     | BVplus
     | BVminus

   let nBasisv=4 (* for matchchecker *)

   let string_of_basisv = function
     | BVzero				-> "|0>"
     | BVone				-> "|1>"
     | BVplus				-> "|+>"
     | BVminus				-> "|->"
 *)
  
type bkelement =
  | BKOne
  | BKZero
  | BKPlus
  | BKMinus
  
type bkconst = bkelement list

let string_of_bkelement = function
  | BKOne       -> "1"
  | BKZero      -> "0"
  | BKPlus      -> "+"
  | BKMinus     -> "-"

let bkelement_of_char = function
  | '1'       -> BKOne
  | '0'       -> BKZero 
  | '+'       -> BKPlus
  | '-'       -> BKMinus
  | c         -> raise (Disaster (Printf.sprintf "bkelement_of_char %c" c))

let bkelements_of_string s =
  List.map bkelement_of_char (List.init (String.length s) (String.get s))

let string_of_bkes es = String.concat "" (List.map string_of_bkelement es)
let string_of_braconst b = "<" ^ string_of_bkes b ^ "|"
let string_of_ketconst k = "|" ^ string_of_bkes k ^ ">"
