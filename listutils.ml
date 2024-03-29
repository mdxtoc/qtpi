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

exception Zip

let zip xs ys = try List.combine xs ys with Invalid_argument _ -> raise Zip
let unzip = List.split

let mirazip xs ys =
  let rec mz rs xs ys =
    match xs,ys with
    | x::xs, y::ys -> mz ((x,y)::rs) xs ys
    | _            -> List.rev rs
  in
  mz [] xs ys

let mirazip2 = mirazip

let mirazip3 xs ys zs = 
  let rec mz rs xs ys zs =
    match xs,ys,zs with
    | x::xs, y::ys, z::zs -> mz ((x,y,z)::rs) xs ys zs
    | _                   -> List.rev rs
  in
  mz [] xs ys zs

(* why don't we have (::)? *)
let cons x xs = x::xs
let null xs = match xs with [] -> true | _ -> false

let (<@>) xys x = List.assoc x xys
let (<@@>) xys x = List.assq x xys

let (<@?>) xys x = List.mem_assoc x xys
let (<@@?>) xys x = List.mem_assq x xys

let (<@+>) xys xy = xy::xys
let (<@@+>)       = (<@+>)

let (<@->) xys x = List.remove_assoc x xys
let (<@@->) xys x = List.remove_assq x xys

let rec invassoc xys y =
  match xys with 
  | [] -> raise Not_found
  | (x,y')::xys -> if y=y' then x else invassoc xys y

let string_of_list fx sep xs = String.concat sep (List.map fx xs)

let bracketed_string_of_list fx xs = "[" ^ string_of_list fx ";" xs ^ "]"

let string_of_multi fx = function
  | [x] -> fx x
  | xs  -> bracketed_string_of_list fx xs
  
let string_of_assoc fx fy colon semicolon xys = 
  String.concat semicolon (List.map (fun (x,y) -> fx x ^ colon ^ fy y) xys)

let numbered xs = Array.to_list (Array.mapi (fun i x -> i,x) (Array.of_list xs))

let zlength xs = Z.of_int (List.length xs)

let tabulate n f = 
  let rec tab acc i = 
    if i<n then tab (f i::acc) (i+1) else List.rev acc
  in 
  tab [] 0

let tabulateZ n f = 
  Z.(let rec tab acc i = 
       if i<n then tab (f i::acc) (i+one) else List.rev acc
     in 
     tab [] zero
    )

let take n xs =
  let rec take rs n xs =
    match n, xs with
    | 0, _
    | _, []     -> List.rev rs
    | _, x::xs  -> take (x::rs) (n-1) xs
  in
  take [] n xs
  
let takewhile p xs =
  let rec take rs xs =
    match xs with
    | []     -> List.rev rs
    | x::xs  -> if p x then take (x::rs) xs else List.rev rs
  in
  take [] xs
  
let rec drop n xs =
  match n, xs with
  | 0, _
  | _, []     -> xs
  | _, x::xs  -> drop (n-1) xs

let takedrop n xs =
  let rec takedrop rs n xs =
    match n, xs with
    | 0, _
    | _, []     -> List.rev rs, xs
    | _, x::xs  -> takedrop (x::rs) (n-1) xs
  in
  takedrop [] n xs

let rec dropwhile p xs =
  match xs with
  | []     -> xs
  | x::xs' -> if p x then dropwhile p xs' else xs

let takedropwhile p xs =
  let rec takedrop rs xs =
    match xs with
    | []     -> List.rev rs, []
    | x::xs' -> if p x then takedrop (x::rs) xs' else List.rev rs, xs
  in
  takedrop [] xs
  
let rec remove x ys =
  match ys with
  | y::ys -> if x=y then ys else y::remove x ys
  | []    -> []

(* as Turner says, this isn't efficient. But I only apply it to very short lists *)  
let rec mkset = function
  | [] -> []
  | x::xs -> x::mkset (List.filter (fun x' -> x<>x') xs)

(* this may be a bit specialised: put pres onto posts in reverse order *)
let rec prepend pres posts = 
  match pres with
  | pre::pres -> prepend pres (pre::posts)
  | []        -> posts

let rec eqlists p xs ys = try List.for_all (uncurry2 p) (List.combine xs ys)
                          with Invalid_argument _ -> false