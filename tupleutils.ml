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
 
let string_of_pair string_of_a string_of_b sep (a,b) =
  Printf.sprintf "%s%s%s" (string_of_a a)
                          sep
                          (string_of_b b)
                          
let bracketed_string_of_pair string_of_a string_of_b pair = 
    "(" ^ string_of_pair string_of_a string_of_b "," pair ^ ")"
    
let string_of_triple string_of_a string_of_b string_of_c sep (a,b,c) =
  Printf.sprintf "%s%s%s%s%s" (string_of_a a)
                              sep
                              (string_of_b b)
                              sep
                              (string_of_c c)
                          
let bracketed_string_of_triple string_of_a string_of_b string_of_c triple = 
    "(" ^ string_of_triple string_of_a string_of_b string_of_c "," triple ^ ")"

let two_map     f   (a,b) = (f a, f b)
let two_fold    f x (a,b) = List.fold_left f x [a;b]
let two_mapfold f x (a,b) = 
  let x, a = f x a in
  let x, b = f x b in
  x, (a,b)

let fstof3  (x,_,_) = x
let sndof3  (_,y,_) = y
let thrdof3 (_,_,z) = z

let three_map     f   (a,b,c) = (f a, f b, f c)
let three_fold    f x (a,b,c) = List.fold_left f x [a;b;c]
let three_mapfold f x (a,b,c) = 
  let x, a = f x a in
  let x, b = f x b in
  let x, c = f x c in
  x, (a,b,c)

