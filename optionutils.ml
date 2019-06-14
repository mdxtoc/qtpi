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

let (||~~) (f: 'a -> 'b) (v: 'b) (opt: 'a option) : 'b = 
  match opt with
  | Some x -> f x
  | None   -> v

let optionpair_either f x g y =
  match f x, g y with
  | None  , None   -> None
  | Some x, None   -> Some (x,y)
  | None  , Some y -> Some (x,y) 
  | Some x, Some y -> Some (x,y)

let optiontriple_either f x g y h z =
  match optionpair_either f x g y, h z with
  | None      , None   -> None
  | None      , Some z -> Some (x,y,z) 
  | Some (x,y), None   -> Some (x,y,z)
  | Some (x,y), Some z -> Some (x,y,z)

(* optmap_all f xs gives Some if f succeeds on all x *)

let rec optmap_all f  = function
| []    -> Some []
| x::xs -> f x &~~ (fun x -> (optmap_all f xs &~~ (fun xs -> Some (x::xs))))

(* optmap_any xs gives Some if f succeeds on any x *)

let rec optmap_any f  = function
| []    -> None
| x::xs -> optionpair_either f x (optmap_any f) xs &~~ (_Some <.> fun (x,xs) -> x::xs)

let rec optfold f x = function
| []      -> None
| y :: ys -> (match f x y with
              | Some x -> Some (anyway (revargs (optfold f) ys) x) 
              | None   -> optfold f x ys
             )
