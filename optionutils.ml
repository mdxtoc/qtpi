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

let string_of_option string_of = function
  | Some x -> "Some (" ^ string_of x ^ ")"
  | None   -> "None"
  
exception Failed_The

let _The = function Some x -> x | None -> raise Failed_The

let _Some x = Some x

let _SomeSome x = Some (Some x)

let bool_of_opt = function Some _ -> true | None -> false

let (&~~) v g =
  match v with 
    None    -> None
  | Some v' -> g v'

let (|~~) v g =
  match v with
    None -> g ()
  | v    -> v

let (&~) f g x = f x &~~ g

let (|~) f g x =
  match f x with
    None -> g x
  | v    -> v

let (||~) f g x =
  match f x with
  | Some x' -> x'
  | None    -> g x

let anyway f = f ||~ id (* same as either x (f x), and to be preferred in those circumstances *)

let rec optfirst optf xs =
  match xs with
  | []    -> None
  | x::xs -> optf x |~~ (fun () -> optfirst optf xs)

