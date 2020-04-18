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

(* I'm a bit embarrassed about this: I wrote these functions before I knew about
   OCaml's for..do..done. I've kept it because I don't want to rewrite everything
   today. But one day ...
 *)
 
let _for i inc n f = (* i<=j<n *)
  let rec rf j =
    if j<n then (f j; rf (j+inc)) (* else skip *)
  in
  rf i
  
let _forZ i inc n f = (* i<=j<n *)
  Z.(let rec rf j =
       if j<n then (f j; rf (j+inc)) (* else skip *)
     in
     rf i
    )
  
let _for_fold_left i inc n v f =
  let rec ff v j =
    if j<n then ff (f v j) (j+inc) else v
  in
  ff v i

let rec _for_fold_right i inc n f v =
  let rec ff j v =
    if i<j then ff (j-inc) (f (j-inc) v) else v
  in
  ff n v

let _for_all i inc n f = 
  let rec ff j =
    j>=n || (f j && ff (j+inc))
  in
  ff i 
  
let _for_exists i inc n f = 
  let rec ff j =
    j<n && (f j || ff (j+inc))
  in
  ff i 

let _for_existsZ i inc n f = 
  Z.(let rec ff j =
       j<n && (f j || ff (j+inc))
     in
     ff i
    ) 
  
