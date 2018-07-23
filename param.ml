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

open Instance
open Listutils
open Name
open Type

(* parameter types get rewritten in typechecking, because we need fully typed
 * processes for resourcing
 *)

type param = (name * _type option ref) instance 

let string_of_param p =
  let n,rt = p.inst in
  match !rt with
  | Some t -> Printf.sprintf "%s:%s" (string_of_name n) (string_of_type t)  
  | None   -> string_of_name n
  
let string_of_params = string_of_list string_of_param ", " 

let strip_param p =
  let n, _ = p.inst in
  n

let strip_params ps = List.map strip_param ps

let param_of_binding pos (n,t) = adorn pos (n, ref (Some t))